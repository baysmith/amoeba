#define AM_IMPLEMENTATION
#include "amoeba.h"

#define am_implemented

#include <assert.h>
#include <float.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define AM_EXTERNAL (0)
#define AM_SLACK (1)
#define AM_ERROR (2)
#define AM_DUMMY (3)

#define am_isexternal(key) (am_Symbol_type(key) == AM_EXTERNAL)
#define am_isslack(key) (am_Symbol_type(key) == AM_SLACK)
#define am_iserror(key) (am_Symbol_type(key) == AM_ERROR)
#define am_isdummy(key) (am_Symbol_type(key) == AM_DUMMY)
#define am_ispivotable(key) (am_isslack(key) || am_iserror(key))

#define AM_POOLSIZE 4096
#define AM_MIN_HASHSIZE 64
#define AM_MAX_SIZET ((~(size_t)0) - 100)

#ifdef AM_USE_FLOAT
#define AM_FLOAT_MAX FLT_MAX
#define AM_FLOAT_EPS 1e-4f
#else
#define AM_FLOAT_MAX DBL_MAX
#define AM_FLOAT_EPS 1e-6
#endif

AM_NS_BEGIN

typedef struct am_Symbol {
    // id first 30 bits, type last 2 bits
    unsigned id_type;
} am_Symbol;
unsigned int am_Symbol_id(am_Symbol sym);
unsigned int am_Symbol_type(am_Symbol sym);
void am_Symbol_set(am_Symbol *sym, unsigned id, unsigned type);

typedef struct am_MemPool {
    size_t size;
    void *freed;
    void *pages;
} am_MemPool;

typedef struct am_Entry {
    int next;
    am_Symbol key;
} am_Entry;

typedef struct am_Table {
    size_t size;
    size_t count;
    size_t entry_size;
    size_t lastfree;
    am_Entry *hash;
} am_Table;

typedef struct am_VarEntry {
    am_Entry entry;
    am_Variable *variable;
} am_VarEntry;

typedef struct am_ConsEntry {
    am_Entry entry;
    am_Constraint *constraint;
} am_ConsEntry;

typedef struct am_Term {
    am_Entry entry;
    am_Float multiplier;
} am_Term;

typedef struct am_Row {
    am_Entry entry;
    am_Symbol infeasible_next;
    am_Table terms;
    am_Float constant;
} am_Row;

struct am_Variable {
    am_Symbol sym;
    am_Symbol dirty_next;
    unsigned refcount;
    am_Solver *solver;
    am_Constraint *constraint;
    am_Float edit_value;
    am_Float value;
};

struct am_Constraint {
    am_Row expression;
    am_Symbol marker;
    am_Symbol other;
    int relation;
    am_Solver *solver;
    am_Float strength;
};

struct am_Solver {
    am_Allocf *allocf;
    void *ud;
    am_Row objective;
    am_Table vars;        /* symbol -> VarEntry */
    am_Table constraints; /* symbol -> ConsEntry */
    am_Table rows;        /* symbol -> Row */
    am_MemPool varpool;
    am_MemPool conspool;
    unsigned symbol_count;
    unsigned constraint_count;
    unsigned auto_update;
    am_Symbol infeasible_rows;
    am_Symbol dirty_vars;
};

int am_nextentry(const am_Table *t, am_Entry **pentry);
int am_approx(am_Float a, am_Float b);

#define am_key(entry) (((am_Entry *)(entry))->key)

#define am_offset(lhs, rhs) ((int)((char *)(lhs) - (char *)(rhs)))
#define am_index(h, i) ((am_Entry *)((char *)(h) + (i)))

    AM_NS_END
