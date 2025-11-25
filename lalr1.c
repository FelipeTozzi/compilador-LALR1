// parser.c
// Implementação didática de gerador de tabelas LALR(1) + parser que constrói árvore de parse.
// Limitações: buffers fixos, resolução de conflitos não automática.
// Compile: gcc -O2 -std=c99 -o lalr_parser parser.c

#define _XOPEN_SOURCE 700
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#define MAX_SYMBOLS 256
#define MAX_TERMINALS 128
#define MAX_NONTERMINALS 128
#define MAX_PRODS 512
#define MAX_RHS 32
#define MAX_ITEMS 4096
#define MAX_STATES 1024
#define MAX_SET_WORDS 4 // bitset for symbols up to 128
#define MAX_NAME_LEN 64
#define MAX_LINE 1024
#define MAX_STACK 4096

// ----- Data structures -----
typedef enum { SYM_TERMINAL=1, SYM_NONTERMINAL=2 } SymType;

typedef struct {
    char name[MAX_NAME_LEN];
    SymType type;
    int id; // 0..N-1
} Symbol;

typedef struct {
    int left; // nonterminal id
    int rhs_len;
    int rhs[MAX_RHS]; // symbol ids
    int index; // production index
} Production;

typedef struct {
    int prod; // production index
    int dot;  // position in RHS (0..rhs_len)
    unsigned long long lookahead[MAX_SET_WORDS]; // bitset of terminals
} Item;

typedef struct {
    Item items[MAX_ITEMS];
    int count;
} ItemSet;

typedef struct {
    ItemSet core; // items representing the core (prod,dot) without lookahead used for merge
    unsigned long long lookahead_union[MAX_SET_WORDS]; // union of lookaheads across core items
    int id;
    ItemSet items; // full items with lookaheads (before merging)
} State;

// Parsing table entries
typedef enum { ACTION_ERR=0, ACTION_SHIFT=1, ACTION_REDUCE=2, ACTION_ACCEPT=3 } ActionType;
typedef struct {
    ActionType type;
    int value; // state for shift, prod for reduce
} ActionEntry;

typedef struct Node {
    int symbol;
    struct Node **children;
    int child_count;
    char *lexeme; // optional token text
} Node;

// ----- Globals -----
int symbol_count = 0;
Symbol sym_table[MAX_SYMBOLS];
int terminal_count = 0;
int nonterminal_count = 0;
int is_terminal[MAX_SYMBOLS];
int term_id[MAX_SYMBOLS]; // maps symbol id to terminal index (0..T-1) or -1
int nonterm_id[MAX_SYMBOLS]; // maps symbol id to nonterm index or -1

Production prods[MAX_PRODS];
int prod_count = 0;
int start_symbol = -1;
int augmented_start_prod = -1;

unsigned long long FIRST[MAX_SYMBOLS][MAX_SET_WORDS];
unsigned long long FOLLOW[MAX_SYMBOLS][MAX_SET_WORDS];
int nullable[MAX_SYMBOLS];

State states[MAX_STATES];
int state_count = 0;

ActionEntry ACTION[MAX_STATES][MAX_TERMINALS];
int GOTO[MAX_STATES][MAX_NONTERMINALS];

int term_sym_id[MAX_TERMINALS];
int nonterm_sym_id[MAX_NONTERMINALS];

// ----- Bitset helpers (for terminals only) -----
static inline void set_bit(unsigned long long *bs, int i) {
    int w = i / 64;
    int b = i % 64;
    bs[w] |= (1ULL << b);
}
static inline int test_bit(unsigned long long *bs, int i) {
    int w = i / 64; int b = i % 64;
    return (bs[w] >> b) & 1ULL;
}
static inline void or_bits(unsigned long long *dst, unsigned long long *src) {
    for(int i=0;i<MAX_SET_WORDS;i++) dst[i] |= src[i];
}
static inline int bits_equal(unsigned long long *a, unsigned long long *b) {
    for(int i=0;i<MAX_SET_WORDS;i++) if(a[i]!=b[i]) return 0;
    return 1;
}
static inline void clear_bits(unsigned long long *a) { for(int i=0;i<MAX_SET_WORDS;i++) a[i]=0ULL; }

// ----- Symbol table -----
int find_symbol(const char *name) {
    for(int i=0;i<symbol_count;i++) if(strcmp(sym_table[i].name, name)==0) return i;
    return -1;
}
int add_symbol(const char *name, SymType type) {
    int id = find_symbol(name);
    if(id>=0) {
        if(sym_table[id].type != type) {
            // allow reclassification? keep original
        }
        return id;
    }
    id = symbol_count++;
    strncpy(sym_table[id].name, name, MAX_NAME_LEN-1);
    sym_table[id].type = type;
    sym_table[id].id = id;
    if(type==SYM_TERMINAL) {
        term_id[id] = terminal_count++;
        is_terminal[id] = 1;
    } else {
        nonterm_id[id] = nonterminal_count++;
        is_terminal[id] = 0;
    }
    return id;
}

// ----- Grammar reader -----
void trim(char *s) {
    char *p = s;
    while(*p && isspace((unsigned char)*p)) p++;
    if(p!=s) memmove(s,p,strlen(p)+1);
    int n = strlen(s);
    while(n>0 && isspace((unsigned char)s[n-1])) s[--n]='\0';
}

void read_grammar(const char *fname) {
    FILE *f = fopen(fname, "r");
    if(!f) { perror("fopen grammar"); exit(1); }
    char line[MAX_LINE];
    // initialize maps
    for(int i=0;i<MAX_SYMBOLS;i++) { term_id[i]=-1; nonterm_id[i]=-1; is_terminal[i]=0; }
    while(fgets(line, sizeof(line), f)) {
        trim(line);
        if(line[0]==0 || line[0]=='#') continue;
        if(strncmp(line, "%token", 6)==0) {
            char *p = line+6;
            while(*p) {
                while(*p && isspace((unsigned char)*p)) p++;
                if(!*p) break;
                char name[MAX_NAME_LEN];
                int i=0;
                while(*p && !isspace((unsigned char)*p)) name[i++]=*p++;
                name[i]=0;
                add_symbol(name, SYM_TERMINAL);
            }
        } else if(strncmp(line, "%start", 6)==0) {
            char nm[MAX_NAME_LEN];
            if(sscanf(line+6, "%s", nm)==1) {
                int id = add_symbol(nm, SYM_NONTERMINAL);
                start_symbol = id;
            }
        } else {
            // production: A -> X Y Z
            char *arrow = strstr(line, "->");
            if(!arrow) { fprintf(stderr, "Invalid production line: %s\n", line); exit(1); }
            char left[MAX_NAME_LEN];
            memset(left,0,sizeof(left));
            int ln = arrow - line;
            // left hand side trim
            char tmp[MAX_LINE]; strncpy(tmp, line, ln); tmp[ln]=0; trim(tmp);
            strcpy(left, tmp);
            int left_id = add_symbol(left, SYM_NONTERMINAL);
            // right side
            char rhs_part[MAX_LINE]; strcpy(rhs_part, arrow+2); trim(rhs_part);
            // split tokens by spaces
            char *tok = strtok(rhs_part, " \t");
            Production p;
            p.left = left_id;
            p.rhs_len = 0;
            p.index = prod_count;

            if (tok) {
                int i=0;
                while(tok && i<MAX_RHS) {
                    if(strcmp(tok, "eps") != 0) {
                        int sym = find_symbol(tok);
                        if(sym==-1) {
                            sym = add_symbol(tok, SYM_NONTERMINAL);
                        }
                        p.rhs[i++] = sym;
                    }
                    tok = strtok(NULL, " \t");
                }
                p.rhs_len = i;
            }

            if(prod_count >= MAX_PRODS) { fprintf(stderr,"too many productions\n"); exit(1); }
            prods[prod_count++] = p;
        }
    }
    fclose(f);
    if(start_symbol==-1) { fprintf(stderr,"start symbol not defined (use %%start)\n"); exit(1); }
    // create augmented start S' -> S
    char augname[MAX_NAME_LEN]; snprintf(augname, sizeof(augname), "%s'", sym_table[start_symbol].name);
    int aug_id = add_symbol(augname, SYM_NONTERMINAL);
    Production p;
    p.left = aug_id;
    p.rhs_len = 1;
    p.rhs[0] = start_symbol;
    p.index = prod_count;
    prods[prod_count++] = p;
    augmented_start_prod = p.index;
    // build nonterminal/terminal counts arrays
    // assign terminal indices (reassign)
    terminal_count = 0; nonterminal_count = 0;
    for(int i=0;i<symbol_count;i++) {
        if(sym_table[i].type==SYM_TERMINAL) {
            term_sym_id[terminal_count] = i;
            term_id[i]=terminal_count++;
            is_terminal[i]=1;
        } else {
            nonterm_sym_id[nonterminal_count] = i;
            nonterm_id[i]=nonterminal_count++;
            is_terminal[i]=0;
        }
    }
}

// ----- FIRST and FOLLOW -----
void compute_first_follow() {
    // initialize
    for(int i=0;i<symbol_count;i++) {
        clear_bits(FIRST[i]);
        clear_bits(FOLLOW[i]);
        nullable[i]=0;
    }
    int eps_id = find_symbol("eps");
    // FIRST for terminals
    for(int i=0;i<symbol_count;i++){
        if(is_terminal[i]) {
            int t = term_id[i];
            if(t>=0) set_bit(FIRST[i], t);
        }
    }
    // iterate to fixpoint
    int changed = 1;
    while(changed) {
        changed = 0;
        for(int pi=0; pi<prod_count; pi++) {
            Production *p = &prods[pi];
            int A = p->left;
            // compute FIRST of RHS
            int all_nullable = 1;
            for(int j=0;j<p->rhs_len;j++) {
                int X = p->rhs[j];
                if(is_terminal[X]) {
                    // add FIRST(X) (terminal itself)
                    int t = term_id[X];
                    if(t>=0 && !test_bit(FIRST[A], t)) { set_bit(FIRST[A], t); changed = 1; }
                    all_nullable = 0;
                    break;
                } else {
                    // add FIRST(X)
                    for(int w=0; w<MAX_SET_WORDS; w++) {
                        unsigned long long before = FIRST[A][w];
                        FIRST[A][w] |= FIRST[X][w];
                        if(FIRST[A][w] != before) changed = 1;
                    }
                    if(!nullable[X]) { all_nullable = 0; break; }
                }
            }
            if(all_nullable) {
                if(!nullable[A]) { nullable[A]=1; changed=1; }
            }
        }
    }
    // FOLLOW
    // init: FOLLOW(start) contains $
    int dollar_term = terminal_count; // we'll reserve index terminal_count for EOF symbol $
    // but our bitset only has MAX_TERMINALS slots. To keep it simple, we will use the 'eps' mechanism:
    // Instead, we'll set FOLLOW of start to include a special terminal index 0 if not conflicting.
    // Simpler: create a pseudo-terminal "$" if not present.
    int dollar_sym = find_symbol("$");
    if(dollar_sym==-1) dollar_sym = add_symbol("$", SYM_TERMINAL);
    // recompute term_id because we added $
    terminal_count = 0;
    for(int i=0;i<symbol_count;i++) if(is_terminal[i]) term_id[i]=terminal_count++; else term_id[i]=-1;
    set_bit(FOLLOW[start_symbol], term_id[dollar_sym]);
    changed = 1;
    while(changed) {
        changed = 0;
        for(int pi=0; pi<prod_count; pi++) {
            Production *p = &prods[pi];
            for(int i=0;i<p->rhs_len;i++) {
                int B = p->rhs[i];
                if(is_terminal[B]) continue;
                // compute FIRST of beta
                unsigned long long first_beta[MAX_SET_WORDS]; clear_bits(first_beta);
                int nullable_beta = 1;
                for(int j=i+1;j<p->rhs_len;j++) {
                    int X = p->rhs[j];
                    if(is_terminal[X]) {
                        set_bit(first_beta, term_id[X]);
                        nullable_beta = 0;
                        break;
                    } else {
                        or_bits(first_beta, FIRST[X]);
                        if(!nullable[X]) { nullable_beta = 0; break; }
                    }
                }
                // add FIRST(beta) - {eps} to FOLLOW(B)
                for(int w=0; w<MAX_SET_WORDS; w++) {
                    unsigned long long before = FOLLOW[B][w];
                    FOLLOW[B][w] |= first_beta[w];
                    if(FOLLOW[B][w] != before) changed = 1;
                }
                if(nullable_beta) {
                    // add FOLLOW(A) to FOLLOW(B)
                    for(int w=0; w<MAX_SET_WORDS; w++) {
                        unsigned long long before = FOLLOW[B][w];
                        FOLLOW[B][w] |= FOLLOW[p->left][w];
                        if(FOLLOW[B][w] != before) changed = 1;
                    }
                }
            }
        }
    }
}

// ----- Item helpers -----
int item_equal_core(const Item *a, const Item *b) {
    return (a->prod == b->prod) && (a->dot == b->dot);
}
int item_equal_full(const Item *a, const Item *b) {
    if(!item_equal_core(a,b)) return 0;
    return bits_equal((unsigned long long*)a->lookahead, (unsigned long long*)b->lookahead);
}

// find item in set (core equality)
int find_item_in_set_core(const ItemSet *set, const Item *it) {
    for(int i=0;i<set->count;i++) if(item_equal_core(&set->items[i], it)) return i;
    return -1;
}
int find_item_in_set_full(const ItemSet *set, const Item *it) {
    for(int i=0;i<set->count;i++) if(item_equal_full(&set->items[i], it)) return i;
    return -1;
}

// add or merge lookahead into an existing item (by core) - returns 1 if changed
int add_or_merge_item(ItemSet *set, const Item *it) {
    int idx = find_item_in_set_core(set, it);
    if(idx==-1) {
        // append
        if(set->count >= MAX_ITEMS) { fprintf(stderr,"too many items in itemset\n"); exit(1); }
        set->items[set->count++] = *it;
        return 1;
    } else {
        int changed = 0;
        for(int w=0; w<MAX_SET_WORDS; w++) {
            unsigned long long before = set->items[idx].lookahead[w];
            set->items[idx].lookahead[w] |= it->lookahead[w];
            if(set->items[idx].lookahead[w] != before) changed = 1;
        }
        return changed;
    }
}

// ----- LR(1) closure and goto -----
void closure_lr1(ItemSet *I) {
    int changed = 1;
    while(changed) {
        changed = 0;
        for(int i=0;i<I->count;i++) {
            Item it = I->items[i];
            if(it.dot >= prods[it.prod].rhs_len) continue;
            int B = prods[it.prod].rhs[it.dot];
            if(is_terminal[B]) continue;
            // compute beta a for lookahead propagation
            // beta = RHS after B
            int beta_len = prods[it.prod].rhs_len - (it.dot+1);
            int beta[MAX_RHS];
            for(int k=0;k<beta_len;k++) beta[k] = prods[it.prod].rhs[it.dot+1+k];
            // for each production B -> gamma, create item B -> . gamma with lookahead = FIRST(beta a)
            for(int pidx=0;pidx<prod_count;pidx++) {
                if(prods[pidx].left != B) continue;
                Item newit; newit.prod = pidx; newit.dot = 0;
                clear_bits(newit.lookahead);
                // compute FIRST(beta followed by lookahead set of it)
                // for each terminal 'a' in it.lookahead add FIRST(beta a)
                // implement: for each terminal t in FIRST(beta) add t; if beta nullable then include it.lookahead
                unsigned long long first_beta[MAX_SET_WORDS]; clear_bits(first_beta);
                int nullable_beta = 1;
                for(int k=0;k<beta_len;k++) {
                    int X = beta[k];
                    if(is_terminal[X]) {
                        set_bit(first_beta, term_id[X]);
                        nullable_beta = 0;
                        break;
                    } else {
                        or_bits(first_beta, FIRST[X]);
                        if(!nullable[X]) { nullable_beta = 0; break; }
                    }
                }
                // add FIRST(beta) terminals to newit.lookahead
                or_bits(newit.lookahead, first_beta);
                if(nullable_beta) {
                    // add lookahead of it
                    or_bits(newit.lookahead, (unsigned long long*)it.lookahead);
                }
                // add or merge into I
                if(add_or_merge_item(I, &newit)) changed = 1;
            }
        }
    }
}

void items_copy(ItemSet *dst, ItemSet *src) {
    dst->count = src->count;
    for(int i=0;i<src->count;i++) dst->items[i] = src->items[i];
}

void goto_lr1(const ItemSet *I, int X, ItemSet *out) {
    out->count = 0;
    for(int i=0;i<I->count;i++) {
        Item it = I->items[i];
        if(it.dot < prods[it.prod].rhs_len && prods[it.prod].rhs[it.dot]==X) {
            Item nit = it; nit.dot++;
            // preserve lookahead
            add_or_merge_item(out, &nit);
        }
    }
    closure_lr1(out);
}

// compare cores of two states
int core_equal(const ItemSet *a, const ItemSet *b) {
    if(a->count != b->count) return 0;
    // compare core items ignoring lookaheads; match by prod and dot sets (order independent)
    int matched[MAX_ITEMS]; memset(matched,0,sizeof(matched));
    for(int i=0;i<a->count;i++) {
        int found = 0;
        for(int j=0;j<b->count;j++) {
            if(matched[j]) continue;
            if(item_equal_core(&a->items[i], &b->items[j])) { matched[j]=1; found=1; break; }
        }
        if(!found) return 0;
    }
    return 1;
}

// ----- Build canonical LR(1) collection then merge cores to LALR(1) -----
int find_state_by_core(ItemSet *core) {
    for(int s=0;s<state_count;s++) {
        if(core_equal(&states[s].core, core)) return s;
    }
    return -1;
}

void build_lr1_states() {
    // initial item: augmented_start_prod with dot 0 and lookahead $
    ItemSet I0; I0.count=0;
    Item it; it.prod = augmented_start_prod; it.dot = 0;
    clear_bits(it.lookahead);
    int dollar_sym = find_symbol("$");
    set_bit(it.lookahead, term_id[dollar_sym]);
    add_or_merge_item(&I0, &it);
    closure_lr1(&I0);
    // create initial state
    states[0].items = I0;
    // core is copy but with lookaheads cleared for core representation (store prod,dot items)
    states[0].core.count = I0.count;
    for(int i=0;i<I0.count;i++) {
        states[0].core.items[i] = I0.items[i];
        clear_bits(states[0].core.items[i].lookahead);
    }
    states[0].id = 0;
    // compute lookahead_union
    for(int w=0;w<MAX_SET_WORDS;w++) states[0].lookahead_union[w]=0ULL;
    for(int i=0;i<I0.count;i++) or_bits(states[0].lookahead_union, (unsigned long long*)I0.items[i].lookahead);
    state_count = 1;
    // BFS over states using symbols (both terminals and nonterminals)
    int changed = 1;
    while(changed) {
        changed = 0;
        for(int s=0;s<state_count;s++) {
            // collect all symbols that can appear after dot
            int seen_sym[MAX_SYMBOLS]; memset(seen_sym,0,sizeof(seen_sym));
            for(int i=0;i<states[s].items.count;i++) {
                Item it = states[s].items.items[i];
                if(it.dot < prods[it.prod].rhs_len) {
                    int X = prods[it.prod].rhs[it.dot];
                    if(!seen_sym[X]) {
                        seen_sym[X]=1;
                        ItemSet gotoSet; gotoSet.count=0;
                        goto_lr1(&states[s].items, X, &gotoSet);
                        if(gotoSet.count==0) continue;
                        // check if there's a state with same core
                        ItemSet coreCopy; coreCopy.count = gotoSet.count;
                        for(int k=0;k<gotoSet.count;k++) { coreCopy.items[k] = gotoSet.items[k]; clear_bits(coreCopy.items[k].lookahead); }
                        int found = find_state_by_core(&coreCopy);
                        if(found==-1) {
                            // new state
                            int nid = state_count;
                            states[nid].items = gotoSet;
                            // core
                            states[nid].core.count = coreCopy.count;
                            for(int k=0;k<coreCopy.count;k++) states[nid].core.items[k] = coreCopy.items[k];
                            // union lookahead
                            for(int w=0;w<MAX_SET_WORDS;w++) states[nid].lookahead_union[w]=0ULL;
                            for(int k=0;k<gotoSet.count;k++) or_bits(states[nid].lookahead_union, (unsigned long long*)gotoSet.items[k].lookahead);
                            states[nid].id = nid;
                            state_count++;
                            changed = 1;
                            if(state_count >= MAX_STATES) { fprintf(stderr,"too many states\n"); exit(1); }
                        } else {
                            // existing: but need to merge lookaheads into state's items (LR(1) collection merging by core)
                            // find state 'found' and merge lookaheads item-wise: for each item in gotoSet, add lookahead into existing state's corresponding item (by core)
                            int changed_local = 0;
                            for(int k=0;k<gotoSet.count;k++) {
                                Item *newit = &gotoSet.items[k];
                                // find matching core item in states[found].items
                                int idx = find_item_in_set_core(&states[found].items, newit);
                                if(idx==-1) {
                                    // append full new item
                                    add_or_merge_item(&states[found].items, newit); changed_local = 1;
                                } else {
                                    for(int w=0; w<MAX_SET_WORDS; w++) {
                                        unsigned long long before = states[found].items.items[idx].lookahead[w];
                                        states[found].items.items[idx].lookahead[w] |= newit->lookahead[w];
                                        if(states[found].items.items[idx].lookahead[w] != before) changed_local = 1;
                                    }
                                }
                            }
                            if(changed_local) changed = 1;
                        }
                    }
                }
            }
        }
    }
    // After constructing LR(1) collection by merging cores when same core created, we already essentially produced LALR(1)
    // However the algorithm above already merges by core: that's LALR behavior.
    // For clarity, we'll rebuild states' core fields and items consistency
    for(int s=0;s<state_count;s++) {
        // ensure core and items coherent
        states[s].core.count = 0;
        for(int i=0;i<states[s].items.count;i++) {
            states[s].core.items[states[s].core.count++] = states[s].items.items[i];
            clear_bits(states[s].core.items[states[s].core.count-1].lookahead);
        }
    }
}

// ----- Build parsing tables -----
void build_parsing_table() {
    // initialize ACTION/GOTO
    for(int s=0;s<state_count;s++) {
        for(int t=0;t<terminal_count;t++) { ACTION[s][t].type = ACTION_ERR; ACTION[s][t].value = -1; }
        for(int A=0;A<nonterminal_count;A++) GOTO[s][A] = -1;
    }
    int dollar_sym = find_symbol("$");
    int dollar_term = term_id[dollar_sym];
    for(int s=0;s<state_count;s++) {
        ItemSet *I = &states[s].items;
        // shifts and gotos: for each item A -> alpha . a beta
        int seen_sym[MAX_SYMBOLS]; memset(seen_sym,0,sizeof(seen_sym));
        for(int i=0;i<I->count;i++) {
            Item it = I->items[i];
            if(it.dot < prods[it.prod].rhs_len) {
                int a = prods[it.prod].rhs[it.dot];
                if(!seen_sym[a]) {
                    // compute goto on a
                    ItemSet gotoSet; gotoSet.count=0;
                    goto_lr1(I, a, &gotoSet);
                    // find state with same core
                    ItemSet coreCopy; coreCopy.count = gotoSet.count;
                    for(int k=0;k<gotoSet.count;k++) { coreCopy.items[k]=gotoSet.items[k]; clear_bits(coreCopy.items[k].lookahead); }
                    int tstate = find_state_by_core(&coreCopy);
                    if(tstate==-1) {
                        fprintf(stderr,"internal: goto target not found\n");
                        exit(1);
                    }
                    if(is_terminal[a]) {
                        // SHIFT
                        int termidx = term_id[a];
                        if(ACTION[s][termidx].type != ACTION_ERR) {
                            // conflict
                            fprintf(stderr,"Conflict at state %d on terminal %s: existing action type %d\n", s, sym_table[a].name, ACTION[s][termidx].type);
                        } else {
                            ACTION[s][termidx].type = ACTION_SHIFT;
                            ACTION[s][termidx].value = tstate;
                        }
                    } else {
                        // GOTO for nonterminal
                        int Aidx = nonterm_id[a];
                        GOTO[s][Aidx] = tstate;
                    }
                    seen_sym[a]=1;
                }
            } else {
                // reduction A -> alpha .
                if(it.prod == augmented_start_prod) {
                    // accept on $
                    ACTION[s][dollar_term].type = ACTION_ACCEPT;
                    ACTION[s][dollar_term].value = 0;
                } else {
                    // for each terminal in lookahead set, add reduce
                    for(int t=0;t<terminal_count;t++) {
                        if(test_bit(it.lookahead, t)) {
                            if(ACTION[s][t].type != ACTION_ERR) {
                                // conflict (report)
                                const char *tname = sym_table[term_sym_id[t]].name;
                                fprintf(stderr,"Conflict at state %d on terminal %s: existing action type %d, trying REDUCE prod %d\n",
                                        s, tname, ACTION[s][t].type, it.prod);
                                // we don't override
                            } else {
                                ACTION[s][t].type = ACTION_REDUCE;
                                ACTION[s][t].value = it.prod;
                            }
                        }
                    }
                }
            }
        }
    }
}

// ----- AST helpers -----
Node *make_node(int symbol) {
    Node *n = malloc(sizeof(Node));
    n->symbol = symbol;
    n->children = NULL;
    n->child_count = 0;
    n->lexeme = NULL;
    return n;
}
Node *make_node_with_children(int symbol, Node **children, int cnt) {
    Node *n = make_node(symbol);
    n->children = malloc(sizeof(Node*) * cnt);
    for(int i=0;i<cnt;i++) n->children[i] = children[i];
    n->child_count = cnt;
    return n;
}
void print_tree(Node *n, int depth) {
    for(int i=0;i<depth;i++) printf("  ");
    printf("%s", sym_table[n->symbol].name);
    if(n->lexeme) printf(" (%s)", n->lexeme);
    printf("\n");
    for(int i=0;i<n->child_count;i++) print_tree(n->children[i], depth+1);
}

void free_tree(Node *n) {
    if (!n) return;
    for (int i = 0; i < n->child_count; i++) {
        free_tree(n->children[i]);
    }
    if (n->children) {
        free(n->children);
    }
    if (n->lexeme) {
        free(n->lexeme);
    }
    free(n);
}

// ----- Parser runtime that uses ACTION/GOTO (reads token stream file) -----
void parse_input(const char *tokfile) {
    // read tokens into array (tokens are symbol names one per line)
    FILE *f = fopen(tokfile, "r");
    if(!f) { perror("fopen tokens"); exit(1); }
    char lines[10000][MAX_NAME_LEN];
    int tcount = 0;
    char buf[MAX_LINE];
    while(fgets(buf, sizeof(buf), f)) {
        trim(buf);
        if(buf[0]==0) continue;
        strncpy(lines[tcount++], buf, MAX_NAME_LEN-1);
    }
    fclose(f);
    // ensure last symbol is $
    if(strcmp(lines[tcount-1], "$")!=0) {
        // append $
        strncpy(lines[tcount++], "$", MAX_NAME_LEN-1);
    }
    // convert to symbol ids
    int tokens[10000]; int token_count = tcount;
    for(int i=0;i<tcount;i++) {
        int id = find_symbol(lines[i]);
        if(id==-1) { fprintf(stderr,"Unknown token in input: %s\n", lines[i]); exit(1); }
        tokens[i] = id;
    }
    // stacks
    int stck_state[MAX_STACK]; Node *stck_node[MAX_STACK];
    int top = 0;
    stck_state[top] = 0;
    stck_node[top] = NULL;
    int ip = 0;
    while(1) {
        int state = stck_state[top];
        int a = tokens[ip];
        if(!is_terminal[a]) { fprintf(stderr,"Input token %s is not terminal\n", sym_table[a].name); exit(1); }
        int termidx = term_id[a];
        ActionEntry act = ACTION[state][termidx];
        if(act.type == ACTION_SHIFT) {
            // create leaf node
            Node *leaf = make_node(a);
            leaf->lexeme = strdup(sym_table[a].name);
            // push state and node
            stck_node[++top] = leaf;
            stck_state[top] = act.value;
            ip++;
        } else if(act.type == ACTION_REDUCE) {
            Production *p = &prods[act.value];
            int k = p->rhs_len;
            Node **kids = NULL;
            if(k>0) {
                kids = malloc(sizeof(Node*) * k);
                for(int i=0;i<k;i++) {
                    kids[k-1-i] = stck_node[top - i]; // collect in order
                }
            }
            // pop k states
            top -= k;
            Node *nnode = make_node_with_children(p->left, kids, k);
            // goto
            int curstate = stck_state[top];
            int Aidx = nonterm_id[p->left];
            int newstate = GOTO[curstate][Aidx];
            if(newstate < 0) {
                fprintf(stderr,"Parse error: no goto from state %d on %s\n", curstate, sym_table[p->left].name);
                exit(1);
            }
            stck_node[++top] = nnode;
            stck_state[top] = newstate;
            // free kids pointer array (nodes retained)
            if(k>0) free(kids);
        } else if(act.type == ACTION_ACCEPT) {
            printf("Parse succeeded. Constructed parse tree:\n");
            Node *root = NULL;
            // The root is the single node on the stack after the augmented production is reduced
            if (top > 0) {
                root = stck_node[top];
            }
            if (root) {
                print_tree(root, 0);
                free_tree(root);
            } else {
                printf("(empty tree)\n");
            }
            return;
        } else {
            fprintf(stderr,"Parse error at token %s (state %d)\n", sym_table[a].name, state);
            return;
        }
    }
}

// ----- utility to dump tables (for debug) -----
void dump_tables() {
    printf("States: %d\n", state_count);
    for(int s=0;s<state_count;s++) {
        printf("State %d:\n", s);
        for(int i=0;i<states[s].items.count;i++) {
            Item *it = &states[s].items.items[i];
            Production *p = &prods[it->prod];
            printf("  %s ->", sym_table[p->left].name);
            for(int k=0;k<p->rhs_len;k++) {
                if(k==it->dot) printf(" .");
                printf(" %s", sym_table[p->rhs[k]].name);
            }
            if(it->dot == p->rhs_len) printf(" .");
            printf("    [");
            for(int t=0;t<terminal_count;t++) if(test_bit(it->lookahead, t)) printf(" %s", sym_table[term_sym_id[t]].name);
            printf(" ]\n");
        }
    }
    printf("\nACTION table (partial):\n");
    for(int s=0;s<state_count;s++) {
        for(int t=0;t<terminal_count;t++) {
            if(ACTION[s][t].type != ACTION_ERR) {
                printf(" ACTION[%d][%s] = ", s, sym_table[term_sym_id[t]].name);
                if(ACTION[s][t].type==ACTION_SHIFT) printf("shift %d\n", ACTION[s][t].value);
                else if(ACTION[s][t].type==ACTION_REDUCE) printf("reduce %d (%s -> ...)\n", ACTION[s][t].value, sym_table[ prods[ACTION[s][t].value].left ].name);
                else if(ACTION[s][t].type==ACTION_ACCEPT) printf("accept\n");
            }
        }
    }
    printf("GOTO table (partial):\n");
    for(int s=0;s<state_count;s++) {
        for(int n=0;n<nonterminal_count;n++) if(GOTO[s][n]>=0) {
            printf(" GOTO[%d][%s] = %d\n", s, sym_table[nonterm_sym_id[n]].name, GOTO[s][n]);
        }
    }
}

// ----- main -----
int main(int argc, char **argv) {
    if(argc < 3) {
        fprintf(stderr,"Usage: %s grammar.txt input.tokens\n", argv[0]);
        fprintf(stderr,"See header comments for grammar format.\n");
        return 1;
    }
    read_grammar(argv[1]);
    compute_first_follow();
    build_lr1_states();
    build_parsing_table();
    dump_tables();
    parse_input(argv[2]);
    return 0;
}
