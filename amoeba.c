#include "amoeba_p.h"

AM_NS_BEGIN

/* utils */

unsigned int am_Symbol_id(am_Symbol sym)
{
    return sym.id_type >> 2;
}
unsigned int am_Symbol_type(am_Symbol sym)
{
    return sym.id_type & 0x3;
}
void am_Symbol_set(am_Symbol *sym, unsigned id, unsigned type)
{
    sym->id_type = (id << 2) | (type & 0x3);
}

static am_Symbol am_newsymbol(am_Solver *solver, int type);

int am_approx(am_Float a, am_Float b)
{
    return a > b ? a - b < AM_FLOAT_EPS : b - a < AM_FLOAT_EPS;
}

static int am_nearzero(am_Float a)
{
    return am_approx(a, 0.0f);
}

static am_Symbol am_null()
{
    am_Symbol null = {0};
    return null;
}

static void am_initsymbol(am_Solver *solver, am_Symbol *sym, int type)
{
    if (am_Symbol_id(*sym) == 0)
        *sym = am_newsymbol(solver, type);
}

static void am_initpool(am_MemPool *pool, size_t size)
{
    pool->size = size;
    pool->freed = pool->pages = NULL;
    assert(size > sizeof(void *) && size < AM_POOLSIZE / 4);
}

static void am_freepool(am_Solver *solver, am_MemPool *pool)
{
    const size_t offset = AM_POOLSIZE - sizeof(void *);
    while (pool->pages != NULL) {
        void *next = *(void **)((char *)pool->pages + offset);
        solver->allocf(solver->ud, pool->pages, 0, AM_POOLSIZE);
        pool->pages = next;
    }
    am_initpool(pool, pool->size);
}

static void *am_alloc(am_Solver *solver, am_MemPool *pool)
{
    void *obj = pool->freed;
    if (obj == NULL) {
        const size_t offset = AM_POOLSIZE - sizeof(void *);
        void *end, *newpage = solver->allocf(solver->ud, NULL, AM_POOLSIZE, 0);
        *(void **)((char *)newpage + offset) = pool->pages;
        pool->pages = newpage;
        end = (char *)newpage + (offset / pool->size - 1) * pool->size;
        while (end != newpage) {
            *(void **)end = pool->freed;
            pool->freed = (void **)end;
            end = (char *)end - pool->size;
        }
        return end;
    }
    pool->freed = *(void **)obj;
    return obj;
}

static void am_free(am_MemPool *pool, void *obj)
{
    *(void **)obj = pool->freed;
    pool->freed = obj;
}

static am_Symbol am_newsymbol(am_Solver *solver, int type)
{
    am_Symbol sym;
    unsigned id = ++solver->symbol_count;
    if (id > 0x3FFFFFFF)
        id = solver->symbol_count = 1;
    assert(type >= AM_EXTERNAL && type <= AM_DUMMY);
    am_Symbol_set(&sym, id, type);
    return sym;
}

/* hash table */

static am_Entry *am_newkey(am_Solver *solver, am_Table *t, am_Symbol key);

static void am_delkey(am_Table *t, am_Entry *entry)
{
    entry->key = am_null(), --t->count;
}

static void am_inittable(am_Table *t, size_t entry_size)
{
    memset(t, 0, sizeof(*t)), t->entry_size = entry_size;
}

static am_Entry *am_mainposition(const am_Table *t, am_Symbol key)
{
    return am_index(t->hash, (am_Symbol_id(key) & (t->size - 1)) * t->entry_size);
}

static void am_resettable(am_Table *t)
{
    t->count = 0;
    memset(t->hash, 0, t->lastfree = t->size * t->entry_size);
}

static size_t am_hashsize(am_Table *t, size_t len)
{
    size_t newsize = AM_MIN_HASHSIZE;
    const size_t max_size = (AM_MAX_SIZET / 2) / t->entry_size;
    while (newsize < max_size && newsize < len)
        newsize <<= 1;
    assert((newsize & (newsize - 1)) == 0);
    return newsize < len ? 0 : newsize;
}

static void am_freetable(am_Solver *solver, am_Table *t)
{
    size_t size = t->size * t->entry_size;
    if (size)
        solver->allocf(solver->ud, t->hash, 0, size);
    am_inittable(t, t->entry_size);
}

static size_t am_resizetable(am_Solver *solver, am_Table *t, size_t len)
{
    size_t i, oldsize = t->size * t->entry_size;
    am_Table nt = *t;
    nt.size = am_hashsize(t, len);
    nt.lastfree = nt.size * nt.entry_size;
    nt.hash = (am_Entry *)solver->allocf(solver->ud, NULL, nt.lastfree, 0);
    memset(nt.hash, 0, nt.size * nt.entry_size);
    for (i = 0; i < oldsize; i += nt.entry_size) {
        am_Entry *e = am_index(t->hash, i);
        if (am_Symbol_id(e->key) != 0) {
            am_Entry *ne = am_newkey(solver, &nt, e->key);
            if (t->entry_size > sizeof(am_Entry))
                memcpy(ne + 1, e + 1, t->entry_size - sizeof(am_Entry));
        }
    }
    if (oldsize)
        solver->allocf(solver->ud, t->hash, 0, oldsize);
    *t = nt;
    return t->size;
}

static am_Entry *am_newkey(am_Solver *solver, am_Table *t, am_Symbol key)
{
    if (t->size == 0)
        am_resizetable(solver, t, AM_MIN_HASHSIZE);
    for (;;) {
        am_Entry *mp = am_mainposition(t, key);
        if (am_Symbol_id(mp->key) != 0) {
            am_Entry *f = NULL, *othern;
            while (t->lastfree > 0) {
                am_Entry *e = am_index(t->hash, t->lastfree -= t->entry_size);
                if (am_Symbol_id(e->key) == 0 && e->next == 0) {
                    f = e;
                    break;
                }
            }
            if (!f) {
                am_resizetable(solver, t, t->count * 2);
                continue;
            }
            assert(am_Symbol_id(f->key) == 0);
            othern = am_mainposition(t, mp->key);
            if (othern != mp) {
                am_Entry *next;
                while ((next = am_index(othern, othern->next)) != mp)
                    othern = next;
                othern->next = am_offset(f, othern);
                memcpy(f, mp, t->entry_size);
                if (mp->next)
                    f->next += am_offset(mp, f), mp->next = 0;
            }
            else {
                if (mp->next != 0)
                    f->next = am_offset(mp, f) + mp->next;
                else
                    assert(f->next == 0);
                mp->next = am_offset(f, mp), mp = f;
            }
        }
        mp->key = key;
        return mp;
    }
}

static const am_Entry *am_gettable(const am_Table *t, am_Symbol key)
{
    const am_Entry *e;
    if (t->size == 0 || am_Symbol_id(key) == 0)
        return NULL;
    e = am_mainposition(t, key);
    for (; am_Symbol_id(e->key) != am_Symbol_id(key); e = am_index(e, e->next))
        if (e->next == 0)
            return NULL;
    return e;
}

static am_Entry *am_settable(am_Solver *solver, am_Table *t, am_Symbol key)
{
    am_Entry *e;
    assert(am_Symbol_id(key) != 0);
    if ((e = (am_Entry *)am_gettable(t, key)) != NULL)
        return e;
    e = am_newkey(solver, t, key);
    if (t->entry_size > sizeof(am_Entry))
        memset(e + 1, 0, t->entry_size - sizeof(am_Entry));
    ++t->count;
    return e;
}

int am_nextentry(const am_Table *t, am_Entry **pentry)
{
    size_t i = *pentry ? am_offset(*pentry, t->hash) + t->entry_size : 0;
    size_t size = t->size * t->entry_size;
    for (; i < size; i += t->entry_size) {
        am_Entry *e = am_index(t->hash, i);
        if (am_Symbol_id(e->key) != 0) {
            *pentry = e;
            return 1;
        }
    }
    *pentry = NULL;
    return 0;
}

/* expression (row) */

static int am_isconstant(am_Row *row)
{
    return row->terms.count == 0;
}

static void am_freerow(am_Solver *solver, am_Row *row)
{
    am_freetable(solver, &row->terms);
}

static void am_resetrow(am_Row *row)
{
    row->constant = 0.0f;
    am_resettable(&row->terms);
}

static void am_initrow(am_Row *row)
{
    am_key(row) = am_null();
    row->infeasible_next = am_null();
    row->constant = 0.0f;
    am_inittable(&row->terms, sizeof(am_Term));
}

static void am_multiply(am_Row *row, am_Float multiplier)
{
    am_Term *term = NULL;
    row->constant *= multiplier;
    while (am_nextentry(&row->terms, (am_Entry **)&term))
        term->multiplier *= multiplier;
}

static void am_addvar(am_Solver *solver, am_Row *row, am_Symbol sym,
                      am_Float value)
{
    am_Term *term;
    if (am_Symbol_id(sym) == 0)
        return;
    if ((term = (am_Term *)am_gettable(&row->terms, sym)) == NULL)
        term = (am_Term *)am_settable(solver, &row->terms, sym);
    if (am_nearzero(term->multiplier += value))
        am_delkey(&row->terms, &term->entry);
}

static void am_addrow(am_Solver *solver, am_Row *row, const am_Row *other,
                      am_Float multiplier)
{
    am_Term *term = NULL;
    row->constant += other->constant * multiplier;
    while (am_nextentry(&other->terms, (am_Entry **)&term))
        am_addvar(solver, row, am_key(term), term->multiplier * multiplier);
}

static void am_solvefor(am_Solver *solver, am_Row *row, am_Symbol entry,
                        am_Symbol exit)
{
    am_Term *term = (am_Term *)am_gettable(&row->terms, entry);
    am_Float reciprocal = 1.0f / term->multiplier;
    assert(am_Symbol_id(entry) != am_Symbol_id(exit) && !am_nearzero(term->multiplier));
    am_delkey(&row->terms, &term->entry);
    am_multiply(row, -reciprocal);
    if (am_Symbol_id(exit) != 0)
        am_addvar(solver, row, exit, reciprocal);
}

static void am_substitute(am_Solver *solver, am_Row *row, am_Symbol entry,
                          const am_Row *other)
{
    am_Term *term = (am_Term *)am_gettable(&row->terms, entry);
    if (!term)
        return;
    am_delkey(&row->terms, &term->entry);
    am_addrow(solver, row, other, term->multiplier);
}

/* variables & constraints */

AM_API int am_variableid(am_Variable *var)
{
    return var ? am_Symbol_id(var->sym) : -1;
}
AM_API am_Float am_value(am_Variable *var)
{
    return var ? var->value : 0.0f;
}
AM_API void am_usevariable(am_Variable *var)
{
    if (var)
        ++var->refcount;
}

static am_Variable *am_sym2var(am_Solver *solver, am_Symbol sym)
{
    am_VarEntry *ve = (am_VarEntry *)am_gettable(&solver->vars, sym);
    assert(ve != NULL);
    return ve->variable;
}

AM_API am_Variable *am_newvariable(am_Solver *solver)
{
    am_Variable *var = (am_Variable *)am_alloc(solver, &solver->varpool);
    am_Symbol sym = am_newsymbol(solver, AM_EXTERNAL);
    am_VarEntry *ve = (am_VarEntry *)am_settable(solver, &solver->vars, sym);
    assert(ve->variable == NULL);
    memset(var, 0, sizeof(*var));
    var->sym = sym;
    var->refcount = 1;
    var->solver = solver;
    ve->variable = var;
    return var;
}

AM_API void am_delvariable(am_Variable *var)
{
    if (var && --var->refcount <= 0) {
        am_Solver *solver = var->solver;
        am_VarEntry *e = (am_VarEntry *)am_gettable(&solver->vars, var->sym);
        assert(e != NULL);
        am_delkey(&solver->vars, &e->entry);
        am_remove(var->constraint);
        am_free(&solver->varpool, var);
    }
}

AM_API am_Constraint *am_newconstraint(am_Solver *solver, am_Float strength)
{
    am_Constraint *cons = (am_Constraint *)am_alloc(solver, &solver->conspool);
    memset(cons, 0, sizeof(*cons));
    cons->solver = solver;
    cons->strength = am_nearzero(strength) ? AM_REQUIRED : strength;
    am_initrow(&cons->expression);
    am_Symbol_set(&am_key(cons), ++solver->constraint_count, AM_EXTERNAL);
    ((am_ConsEntry *)am_settable(solver, &solver->constraints, am_key(cons)))
        ->constraint = cons;
    return cons;
}

AM_API void am_delconstraint(am_Constraint *cons)
{
    am_Solver *solver = cons ? cons->solver : NULL;
    am_Term *term = NULL;
    am_ConsEntry *ce;
    if (cons == NULL)
        return;
    am_remove(cons);
    ce = (am_ConsEntry *)am_gettable(&solver->constraints, am_key(cons));
    assert(ce != NULL);
    am_delkey(&solver->constraints, &ce->entry);
    while (am_nextentry(&cons->expression.terms, (am_Entry **)&term))
        am_delvariable(am_sym2var(solver, am_key(term)));
    am_freerow(solver, &cons->expression);
    am_free(&solver->conspool, cons);
}

AM_API am_Constraint *am_cloneconstraint(am_Constraint *other,
                                         am_Float strength)
{
    am_Constraint *cons;
    if (other == NULL)
        return NULL;
    cons = am_newconstraint(other->solver,
                            am_nearzero(strength) ? other->strength : strength);
    am_mergeconstraint(cons, other, 1.0f);
    cons->relation = other->relation;
    return cons;
}

AM_API int am_mergeconstraint(am_Constraint *cons, am_Constraint *other,
                              am_Float multiplier)
{
    am_Term *term = NULL;
    if (cons == NULL || other == NULL || am_Symbol_id(cons->marker) != 0 ||
        cons->solver != other->solver)
        return AM_FAILED;
    if (cons->relation == AM_GREATEQUAL)
        multiplier = -multiplier;
    cons->expression.constant += other->expression.constant * multiplier;
    while (am_nextentry(&other->expression.terms, (am_Entry **)&term)) {
        am_usevariable(am_sym2var(cons->solver, am_key(term)));
        am_addvar(cons->solver, &cons->expression, am_key(term),
                  term->multiplier * multiplier);
    }
    return AM_OK;
}

AM_API void am_resetconstraint(am_Constraint *cons)
{
    am_Term *term = NULL;
    if (cons == NULL)
        return;
    am_remove(cons);
    cons->relation = 0;
    while (am_nextentry(&cons->expression.terms, (am_Entry **)&term))
        am_delvariable(am_sym2var(cons->solver, am_key(term)));
    am_resetrow(&cons->expression);
}

AM_API int am_addterm(am_Constraint *cons, am_Variable *var,
                      am_Float multiplier)
{
    if (cons == NULL || var == NULL || am_Symbol_id(cons->marker) != 0 ||
        cons->solver != var->solver)
        return AM_FAILED;
    assert(am_Symbol_id(var->sym) != 0);
    assert(var->solver == cons->solver);
    if (cons->relation == AM_GREATEQUAL)
        multiplier = -multiplier;
    am_addvar(cons->solver, &cons->expression, var->sym, multiplier);
    am_usevariable(var);
    return AM_OK;
}

AM_API int am_addconstant(am_Constraint *cons, am_Float constant)
{
    if (cons == NULL || am_Symbol_id(cons->marker) != 0)
        return AM_FAILED;
    if (cons->relation == AM_GREATEQUAL)
        cons->expression.constant -= constant;
    else
        cons->expression.constant += constant;
    return AM_OK;
}

AM_API int am_setrelation(am_Constraint *cons, int relation)
{
    assert(relation >= AM_LESSEQUAL && relation <= AM_GREATEQUAL);
    if (cons == NULL || am_Symbol_id(cons->marker) != 0 || cons->relation != 0)
        return AM_FAILED;
    if (relation != AM_GREATEQUAL)
        am_multiply(&cons->expression, -1.0f);
    cons->relation = relation;
    return AM_OK;
}

/* Cassowary algorithm */

AM_API int am_hasedit(am_Variable *var)
{
    return var != NULL && var->constraint != NULL;
}

AM_API int am_hasconstraint(am_Constraint *cons)
{
    return cons != NULL && am_Symbol_id(cons->marker) != 0;
}

AM_API void am_autoupdate(am_Solver *solver, int auto_update)
{
    solver->auto_update = auto_update;
}

static void am_infeasible(am_Solver *solver, am_Row *row)
{
    if (am_isdummy(row->infeasible_next))
        return;
    am_Symbol_set(&(row->infeasible_next), am_Symbol_id(solver->infeasible_rows), AM_DUMMY);
    solver->infeasible_rows = am_key(row);
}

static void am_markdirty(am_Solver *solver, am_Variable *var)
{
    if (am_Symbol_type(var->dirty_next) == AM_DUMMY)
        return;
    am_Symbol_set(&(var->dirty_next), am_Symbol_id(solver->dirty_vars), AM_DUMMY);
    solver->dirty_vars = var->sym;
}

static void am_substitute_rows(am_Solver *solver, am_Symbol var, am_Row *expr)
{
    am_Row *row = NULL;
    while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
        am_substitute(solver, row, var, expr);
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row->constant < 0.0f)
            am_infeasible(solver, row);
    }
    am_substitute(solver, &solver->objective, var, expr);
}

static int am_getrow(am_Solver *solver, am_Symbol sym, am_Row *dst)
{
    am_Row *row = (am_Row *)am_gettable(&solver->rows, sym);
    am_key(dst) = am_null();
    if (row == NULL)
        return AM_FAILED;
    am_delkey(&solver->rows, &row->entry);
    dst->constant = row->constant;
    dst->terms = row->terms;
    return AM_OK;
}

static int am_putrow(am_Solver *solver, am_Symbol sym, const am_Row *src)
{
    am_Row *row = (am_Row *)am_settable(solver, &solver->rows, sym);
    row->constant = src->constant;
    row->terms = src->terms;
    return AM_OK;
}

static void am_mergerow(am_Solver *solver, am_Row *row, am_Symbol var,
                        am_Float multiplier)
{
    am_Row *oldrow = (am_Row *)am_gettable(&solver->rows, var);
    if (oldrow)
        am_addrow(solver, row, oldrow, multiplier);
    else
        am_addvar(solver, row, var, multiplier);
}

static int am_optimize(am_Solver *solver, am_Row *objective)
{
    for (;;) {
        am_Symbol enter = am_null(), exit = am_null();
        am_Float r, min_ratio = AM_FLOAT_MAX;
        am_Row tmp, *row = NULL;
        am_Term *term = NULL;

        assert(am_Symbol_id(solver->infeasible_rows) == 0);
        while (am_nextentry(&objective->terms, (am_Entry **)&term)) {
            if (!am_isdummy(am_key(term)) && term->multiplier < 0.0f) {
                enter = am_key(term);
                break;
            }
        }
        if (am_Symbol_id(enter) == 0)
            return AM_OK;

        while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
            term = (am_Term *)am_gettable(&row->terms, enter);
            if (term == NULL || !am_ispivotable(am_key(row)) ||
                term->multiplier > 0.0f)
                continue;
            r = -row->constant / term->multiplier;
            if (r < min_ratio ||
                (am_approx(r, min_ratio) && am_Symbol_id(am_key(row)) < am_Symbol_id(exit)))
                min_ratio = r, exit = am_key(row);
        }
        assert(am_Symbol_id(exit) != 0);
        if (am_Symbol_id(exit) == 0)
            return AM_FAILED;

        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, enter, exit);
        am_substitute_rows(solver, enter, &tmp);
        if (objective != &solver->objective)
            am_substitute(solver, objective, enter, &tmp);
        am_putrow(solver, enter, &tmp);
    }
}

static am_Row am_makerow(am_Solver *solver, am_Constraint *cons)
{
    am_Term *term = NULL;
    am_Row row;
    am_initrow(&row);
    row.constant = cons->expression.constant;
    while (am_nextentry(&cons->expression.terms, (am_Entry **)&term)) {
        am_markdirty(solver, am_sym2var(solver, am_key(term)));
        am_mergerow(solver, &row, am_key(term), term->multiplier);
    }
    if (cons->relation != AM_EQUAL) {
        am_initsymbol(solver, &cons->marker, AM_SLACK);
        am_addvar(solver, &row, cons->marker, -1.0f);
        if (cons->strength < AM_REQUIRED) {
            am_initsymbol(solver, &cons->other, AM_ERROR);
            am_addvar(solver, &row, cons->other, 1.0f);
            am_addvar(solver, &solver->objective, cons->other, cons->strength);
        }
    }
    else if (cons->strength >= AM_REQUIRED) {
        am_initsymbol(solver, &cons->marker, AM_DUMMY);
        am_addvar(solver, &row, cons->marker, 1.0f);
    }
    else {
        am_initsymbol(solver, &cons->marker, AM_ERROR);
        am_initsymbol(solver, &cons->other, AM_ERROR);
        am_addvar(solver, &row, cons->marker, -1.0f);
        am_addvar(solver, &row, cons->other, 1.0f);
        am_addvar(solver, &solver->objective, cons->marker, cons->strength);
        am_addvar(solver, &solver->objective, cons->other, cons->strength);
    }
    if (row.constant < 0.0f)
        am_multiply(&row, -1.0f);
    return row;
}

static void am_remove_errors(am_Solver *solver, am_Constraint *cons)
{
    if (am_iserror(cons->marker))
        am_mergerow(solver, &solver->objective, cons->marker, -cons->strength);
    if (am_iserror(cons->other))
        am_mergerow(solver, &solver->objective, cons->other, -cons->strength);
    if (am_isconstant(&solver->objective))
        solver->objective.constant = 0.0f;
    cons->marker = cons->other = am_null();
}

static int am_add_with_artificial(am_Solver *solver, am_Row *row,
                                  am_Constraint *cons)
{
    am_Symbol a = am_newsymbol(solver, AM_SLACK);
    am_Term *term = NULL;
    am_Row tmp;
    int ret;
    --solver->symbol_count; /* artificial variable will be removed */
    am_initrow(&tmp);
    am_addrow(solver, &tmp, row, 1.0f);
    am_putrow(solver, a, row);
    am_initrow(row), row = NULL; /* row is useless */
    am_optimize(solver, &tmp);
    ret = am_nearzero(tmp.constant) ? AM_OK : AM_UNBOUND;
    am_freerow(solver, &tmp);
    if (am_getrow(solver, a, &tmp) == AM_OK) {
        am_Symbol entry = am_null();
        if (am_isconstant(&tmp)) {
            am_freerow(solver, &tmp);
            return ret;
        }
        while (am_nextentry(&tmp.terms, (am_Entry **)&term))
            if (am_ispivotable(am_key(term))) {
                entry = am_key(term);
                break;
            }
        if (am_Symbol_id(entry) == 0) {
            am_freerow(solver, &tmp);
            return AM_UNBOUND;
        }
        am_solvefor(solver, &tmp, entry, a);
        am_substitute_rows(solver, entry, &tmp);
        am_putrow(solver, entry, &tmp);
    }
    while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
        term = (am_Term *)am_gettable(&row->terms, a);
        if (term)
            am_delkey(&row->terms, &term->entry);
    }
    term = (am_Term *)am_gettable(&solver->objective.terms, a);
    if (term)
        am_delkey(&solver->objective.terms, &term->entry);
    if (ret != AM_OK)
        am_remove(cons);
    return ret;
}

static int am_try_addrow(am_Solver *solver, am_Row *row, am_Constraint *cons)
{
    am_Symbol subject = am_null();
    am_Term *term = NULL;
    while (am_nextentry(&row->terms, (am_Entry **)&term))
        if (am_isexternal(am_key(term))) {
            subject = am_key(term);
            break;
        }
    if (am_Symbol_id(subject) == 0 && am_ispivotable(cons->marker)) {
        am_Term *mterm = (am_Term *)am_gettable(&row->terms, cons->marker);
        if (mterm->multiplier < 0.0f)
            subject = cons->marker;
    }
    if (am_Symbol_id(subject) == 0 && am_ispivotable(cons->other)) {
        am_Term *mterm = (am_Term *)am_gettable(&row->terms, cons->other);
        if (mterm->multiplier < 0.0f)
            subject = cons->other;
    }
    if (am_Symbol_id(subject) == 0) {
        while (am_nextentry(&row->terms, (am_Entry **)&term))
            if (!am_isdummy(am_key(term)))
                break;
        if (term == NULL) {
            if (am_nearzero(row->constant))
                subject = cons->marker;
            else {
                am_freerow(solver, row);
                return AM_UNSATISFIED;
            }
        }
    }
    if (am_Symbol_id(subject) == 0)
        return am_add_with_artificial(solver, row, cons);
    am_solvefor(solver, row, subject, am_null());
    am_substitute_rows(solver, subject, row);
    am_putrow(solver, subject, row);
    return AM_OK;
}

static am_Symbol am_get_leaving_row(am_Solver *solver, am_Symbol marker)
{
    am_Symbol first = am_null(), second = am_null(), third = am_null();
    am_Float r1 = AM_FLOAT_MAX, r2 = AM_FLOAT_MAX;
    am_Row *row = NULL;
    while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
        am_Term *term = (am_Term *)am_gettable(&row->terms, marker);
        if (term == NULL)
            continue;
        if (am_isexternal(am_key(row)))
            third = am_key(row);
        else if (term->multiplier < 0.0f) {
            am_Float r = -row->constant / term->multiplier;
            if (r < r1)
                r1 = r, first = am_key(row);
        }
        else {
            am_Float r = row->constant / term->multiplier;
            if (r < r2)
                r2 = r, second = am_key(row);
        }
    }
    return am_Symbol_id(first) ? first : am_Symbol_id(second) ? second : third;
}

static void am_delta_edit_constant(am_Solver *solver, am_Float delta,
                                   am_Constraint *cons)
{
    am_Row *row;
    if ((row = (am_Row *)am_gettable(&solver->rows, cons->marker)) != NULL) {
        if ((row->constant -= delta) < 0.0f)
            am_infeasible(solver, row);
        return;
    }
    if ((row = (am_Row *)am_gettable(&solver->rows, cons->other)) != NULL) {
        if ((row->constant += delta) < 0.0f)
            am_infeasible(solver, row);
        return;
    }
    while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
        am_Term *term = (am_Term *)am_gettable(&row->terms, cons->marker);
        if (term == NULL)
            continue;
        row->constant += term->multiplier * delta;
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row->constant < 0.0f)
            am_infeasible(solver, row);
    }
}

static void am_dual_optimize(am_Solver *solver)
{
    while (am_Symbol_id(solver->infeasible_rows) != 0) {
        am_Row tmp, *row = (am_Row *)am_gettable(&solver->rows,
                                                 solver->infeasible_rows);
        am_Symbol enter = am_null(), exit = am_key(row), curr;
        am_Term *objterm, *term = NULL;
        am_Float r, min_ratio = AM_FLOAT_MAX;
        solver->infeasible_rows = row->infeasible_next;
        row->infeasible_next = am_null();
        if (row->constant >= 0.0f)
            continue;
        while (am_nextentry(&row->terms, (am_Entry **)&term)) {
            if (am_isdummy(curr = am_key(term)) || term->multiplier <= 0.0f)
                continue;
            objterm = (am_Term *)am_gettable(&solver->objective.terms, curr);
            r = objterm ? objterm->multiplier / term->multiplier : 0.0f;
            if (min_ratio > r)
                min_ratio = r, enter = curr;
        }
        assert(am_Symbol_id(enter) != 0);
        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, enter, exit);
        am_substitute_rows(solver, enter, &tmp);
        am_putrow(solver, enter, &tmp);
    }
}

static void *am_default_allocf(void *ud, void *ptr, size_t nsize, size_t osize)
{
    void *newptr;
    (void)ud, (void)osize;
    if (nsize == 0) {
        free(ptr);
        return NULL;
    }
    newptr = realloc(ptr, nsize);
    if (newptr == NULL)
        abort();
    return newptr;
}

AM_API am_Solver *am_newsolver(am_Allocf *allocf, void *ud)
{
    am_Solver *solver;
    if (allocf == NULL)
        allocf = am_default_allocf;
    if ((solver = (am_Solver *)allocf(ud, NULL, sizeof(am_Solver), 0)) == NULL)
        return NULL;
    memset(solver, 0, sizeof(*solver));
    solver->allocf = allocf;
    solver->ud = ud;
    am_initrow(&solver->objective);
    am_inittable(&solver->vars, sizeof(am_VarEntry));
    am_inittable(&solver->constraints, sizeof(am_ConsEntry));
    am_inittable(&solver->rows, sizeof(am_Row));
    am_initpool(&solver->varpool, sizeof(am_Variable));
    am_initpool(&solver->conspool, sizeof(am_Constraint));
    return solver;
}

AM_API void am_delsolver(am_Solver *solver)
{
    am_ConsEntry *ce = NULL;
    am_Row *row = NULL;
    while (am_nextentry(&solver->constraints, (am_Entry **)&ce))
        am_freerow(solver, &ce->constraint->expression);
    while (am_nextentry(&solver->rows, (am_Entry **)&row))
        am_freerow(solver, row);
    am_freerow(solver, &solver->objective);
    am_freetable(solver, &solver->vars);
    am_freetable(solver, &solver->constraints);
    am_freetable(solver, &solver->rows);
    am_freepool(solver, &solver->varpool);
    am_freepool(solver, &solver->conspool);
    solver->allocf(solver->ud, solver, 0, sizeof(*solver));
}

AM_API void am_resetsolver(am_Solver *solver, int clear_constraints)
{
    am_Entry *entry = NULL;
    if (!solver->auto_update)
        am_updatevars(solver);
    while (am_nextentry(&solver->vars, &entry)) {
        am_Constraint **cons = &((am_VarEntry *)entry)->variable->constraint;
        am_remove(*cons);
        *cons = NULL;
    }
    assert(am_nearzero(solver->objective.constant));
    assert(am_Symbol_id(solver->infeasible_rows) == 0);
    assert(am_Symbol_id(solver->dirty_vars) == 0);
    if (!clear_constraints)
        return;
    am_resetrow(&solver->objective);
    while (am_nextentry(&solver->constraints, &entry)) {
        am_Constraint *cons = ((am_ConsEntry *)entry)->constraint;
        if (am_Symbol_id(cons->marker) == 0)
            continue;
        cons->marker = cons->other = am_null();
    }
    while (am_nextentry(&solver->rows, &entry)) {
        am_delkey(&solver->rows, entry);
        am_freerow(solver, (am_Row *)entry);
    }
}

AM_API void am_updatevars(am_Solver *solver)
{
    while (am_Symbol_id(solver->dirty_vars) != 0) {
        am_Variable *var = am_sym2var(solver, solver->dirty_vars);
        am_Row *row = (am_Row *)am_gettable(&solver->rows, var->sym);
        solver->dirty_vars = var->dirty_next;
        var->dirty_next = am_null();
        var->value = row ? row->constant : 0.0f;
    }
}

AM_API int am_add(am_Constraint *cons)
{
    am_Solver *solver = cons ? cons->solver : NULL;
    int ret, oldsym = solver ? solver->symbol_count : 0;
    am_Row row;
    if (solver == NULL || am_Symbol_id(cons->marker) != 0)
        return AM_FAILED;
    row = am_makerow(solver, cons);
    if ((ret = am_try_addrow(solver, &row, cons)) != AM_OK) {
        am_remove_errors(solver, cons);
        solver->symbol_count = oldsym;
    }
    else {
        am_optimize(solver, &solver->objective);
        if (solver->auto_update)
            am_updatevars(solver);
    }
    return ret;
}

AM_API void am_remove(am_Constraint *cons)
{
    am_Solver *solver;
    am_Symbol marker;
    am_Row tmp;
    if (cons == NULL || am_Symbol_id(cons->marker) == 0)
        return;
    solver = cons->solver, marker = cons->marker;
    am_remove_errors(solver, cons);
    if (am_getrow(solver, marker, &tmp) != AM_OK) {
        am_Symbol exit = am_get_leaving_row(solver, marker);
        assert(am_Symbol_id(exit) != 0);
        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, marker, exit);
        am_substitute_rows(solver, marker, &tmp);
    }
    am_freerow(solver, &tmp);
    am_optimize(solver, &solver->objective);
    if (solver->auto_update)
        am_updatevars(solver);
}

AM_API int am_setstrength(am_Constraint *cons, am_Float strength)
{
    if (cons == NULL)
        return AM_FAILED;
    strength = am_nearzero(strength) ? AM_REQUIRED : strength;
    if (cons->strength == strength)
        return AM_OK;
    if (cons->strength >= AM_REQUIRED || strength >= AM_REQUIRED) {
        am_remove(cons), cons->strength = strength;
        return am_add(cons);
    }
    if (am_Symbol_id(cons->marker) != 0) {
        am_Solver *solver = cons->solver;
        am_Float diff = strength - cons->strength;
        am_mergerow(solver, &solver->objective, cons->marker, diff);
        am_mergerow(solver, &solver->objective, cons->other, diff);
        am_optimize(solver, &solver->objective);
        if (solver->auto_update)
            am_updatevars(solver);
    }
    cons->strength = strength;
    return AM_OK;
}

AM_API int am_addedit(am_Variable *var, am_Float strength)
{
    am_Solver *solver = var ? var->solver : NULL;
    am_Constraint *cons;
    if (var == NULL || var->constraint != NULL)
        return AM_FAILED;
    assert(am_Symbol_id(var->sym) != 0);
    if (strength >= AM_STRONG)
        strength = AM_STRONG;
    cons = am_newconstraint(solver, strength);
    am_setrelation(cons, AM_EQUAL);
    am_addterm(cons, var, 1.0f); /* var must have positive signture */
    am_addconstant(cons, -var->value);
    if (am_add(cons) != AM_OK)
        assert(0);
    var->constraint = cons;
    var->edit_value = var->value;
    return AM_OK;
}

AM_API void am_deledit(am_Variable *var)
{
    if (var == NULL || var->constraint == NULL)
        return;
    am_delconstraint(var->constraint);
    var->constraint = NULL;
    var->edit_value = 0.0f;
}

AM_API void am_suggest(am_Variable *var, am_Float value)
{
    am_Solver *solver = var ? var->solver : NULL;
    am_Float delta;
    if (var == NULL)
        return;
    if (var->constraint == NULL) {
        am_addedit(var, AM_MEDIUM);
        assert(var->constraint != NULL);
    }
    delta = value - var->edit_value;
    var->edit_value = value;
    am_delta_edit_constant(solver, delta, var->constraint);
    am_dual_optimize(solver);
    if (solver->auto_update)
        am_updatevars(solver);
}

AM_NS_END
