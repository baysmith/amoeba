#define AM_IMPLEMENTATION
#include "amoeba.h"

#include <assert.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

static jmp_buf jbuf;
static size_t allmem = 0;
static size_t maxmem = 0;
static void *END = NULL;

static void *debug_allocf(void *ud, void *ptr, size_t ns, size_t os)
{
    void *newptr = NULL;
    (void)ud;
    allmem += ns;
    allmem -= os;
    if (maxmem < allmem)
        maxmem = allmem;
    if (ns == 0)
        free(ptr);
    else {
        newptr = realloc(ptr, ns);
        if (newptr == NULL)
            longjmp(jbuf, 1);
    }
#ifdef DEBUG_MEMORY
    printf("new(%p):\t+%d, old(%p):\t-%d\n", newptr, (int)ns, ptr, (int)os);
#endif
    return newptr;
}

static void *null_allocf(void *ud, void *ptr, size_t ns, size_t os)
{
    (void)ud, (void)ptr, (void)ns, (void)os;
    return NULL;
}

static void am_dumpkey(am_Symbol sym)
{
    int ch = 'v';
    switch (sym.type) {
    case AM_EXTERNAL:
        ch = 'v';
        break;
    case AM_SLACK:
        ch = 's';
        break;
    case AM_ERROR:
        ch = 'e';
        break;
    case AM_DUMMY:
        ch = 'd';
        break;
    }
    printf("%c%d", ch, (int)sym.id);
}

static void am_dumprow(am_Row *row)
{
    am_Term *term = NULL;
    printf("%g", row->constant);
    while (am_nextentry(&row->terms, (am_Entry **)&term)) {
        am_Float multiplier = term->multiplier;
        printf(" %c ", multiplier > 0.0 ? '+' : '-');
        if (multiplier < 0.0)
            multiplier = -multiplier;
        if (!am_approx(multiplier, 1.0f))
            printf("%g*", multiplier);
        am_dumpkey(am_key(term));
    }
    printf("\n");
}

static void am_dumpsolver(am_Solver *solver)
{
    if (!solver)
        return;
    am_Row *row = NULL;
    int idx = 0;
    printf("-------------------------------\n");
    printf("solver: ");
    am_dumprow(&solver->objective);
    printf("rows(%d):\n", (int)solver->rows.count);
    while (am_nextentry(&solver->rows, (am_Entry **)&row)) {
        printf("%d. ", ++idx);
        am_dumpkey(am_key(row));
        printf(" = ");
        am_dumprow(row);
    }
    printf("-------------------------------\n");
}

static am_Constraint *new_constraint(am_Solver *in_solver, double in_strength,
                                     am_Variable *in_term1, double in_factor1,
                                     int in_relation, double in_constant, ...)
{
    int result;
    va_list argp;
    am_Constraint *c;
    assert(in_solver && in_term1);
    c = am_newconstraint(in_solver, (am_Float)in_strength);
    if (!c)
        return 0;
    am_addterm(c, in_term1, (am_Float)in_factor1);
    am_setrelation(c, in_relation);
    if (in_constant)
        am_addconstant(c, (am_Float)in_constant);
    va_start(argp, in_constant);
    while (1) {
        am_Variable *va_term = va_arg(argp, am_Variable *);
        double va_factor = va_arg(argp, double);
        if (va_term == 0)
            break;
        am_addterm(c, va_term, (am_Float)va_factor);
    }
    va_end(argp);
    result = am_add(c);
    assert(result == AM_OK);
    return c;
}

static void test_all()
{
    printf("test_all...\n");
    am_Solver *solver;
    am_Variable *xl;
    am_Variable *xm;
    am_Variable *xr;
    am_Variable *xd;
    am_Constraint *c1, *c2, *c3, *c4, *c5, *c6;
    int ret = setjmp(jbuf);
    if (ret < 0) {
        perror("setjmp");
        return;
    }
    else if (ret != 0) {
        printf("out of memory!\n");
        return;
    }

    solver = am_newsolver(null_allocf, NULL);
    assert(solver == NULL);

    solver = am_newsolver(NULL, NULL);
    assert(solver != NULL);
    am_delsolver(solver);

    solver = am_newsolver(debug_allocf, NULL);
    xl = am_newvariable(solver);
    xm = am_newvariable(solver);
    xr = am_newvariable(solver);

    assert(am_variableid(NULL) == -1);
    assert(am_variableid(xl) == 1);
    assert(am_variableid(xm) == 2);
    assert(am_variableid(xr) == 3);
    assert(!am_hasedit(NULL));
    assert(!am_hasedit(xl));
    assert(!am_hasedit(xm));
    assert(!am_hasedit(xr));
    assert(!am_hasconstraint(NULL));

    xd = am_newvariable(solver);
    am_delvariable(xd);

    assert(am_setrelation(NULL, AM_GREATEQUAL) == AM_FAILED);

    c1 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c1, xl, 1.0);
    am_setrelation(c1, AM_GREATEQUAL);
    ret = am_add(c1);
    assert(ret == AM_OK);
    assert(solver->rows.count == 1);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);

    assert(am_setrelation(c1, AM_GREATEQUAL) == AM_FAILED);
    assert(am_setstrength(c1, AM_REQUIRED - 10) == AM_OK);
    assert(am_setstrength(c1, AM_REQUIRED) == AM_OK);

    assert(am_hasconstraint(c1));
    assert(!am_hasedit(xl));

    c2 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c2, xl, 1.0);
    am_setrelation(c2, AM_EQUAL);
    ret = am_add(c2);
    assert(ret == AM_OK);
    assert(solver->rows.count == 2);

    am_resetsolver(solver, 1);
    am_delconstraint(c1);
    am_delconstraint(c2);
    assert(solver->rows.count == 0);

    /* c1: 2*xm == xl + xr */
    c1 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c1, xm, 2.0);
    am_setrelation(c1, AM_EQUAL);
    am_addterm(c1, xl, 1.0);
    am_addterm(c1, xr, 1.0);
    ret = am_add(c1);
    assert(ret == AM_OK);
    assert(solver->rows.count == 1);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 0.0);
    assert(am_value(xr) == 0.0);
    am_suggest(xm, 4.0);
    am_updatevars(solver);
    assert(am_value(xl) == 8.0);
    assert(am_value(xm) == 4.0);
    assert(am_value(xr) == 0.0);
    am_suggest(xr, 2.0);
    am_updatevars(solver);
    assert(am_value(xl) == 6.0);
    assert(am_value(xm) == 4.0);
    assert(am_value(xr) == 2.0);

    /* c2: xl + 10 <= xr */
    c2 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c2, xl, 1.0);
    am_addconstant(c2, 10.0);
    am_setrelation(c2, AM_LESSEQUAL);
    am_addterm(c2, xr, 1.0);
    ret = am_add(c2);
    assert(ret == AM_OK);
    assert(solver->rows.count == 4);
    am_updatevars(solver);
    assert(am_value(xl) == -8.0);
    assert(am_value(xm) == -3.0);
    assert(am_value(xr) == 2.0);

    /* c3: xr <= 100 */
    c3 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c3, xr, 1.0);
    am_setrelation(c3, AM_LESSEQUAL);
    am_addconstant(c3, 100.0);
    ret = am_add(c3);
    assert(ret == AM_OK);
    assert(solver->rows.count == 5);
    am_updatevars(solver);
    assert(am_value(xl) == -8.0);
    assert(am_value(xm) == -3.0);
    assert(am_value(xr) == 2.0);

    /* c4: xl >= 0 */
    c4 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c4, xl, 1.0);
    am_setrelation(c4, AM_GREATEQUAL);
    am_addconstant(c4, 0.0);
    ret = am_add(c4);
    assert(ret == AM_OK);
    assert(solver->rows.count == 6);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 5.0);
    assert(am_value(xr) == 10.0);

    c5 = am_cloneconstraint(c4, AM_REQUIRED);
    ret = am_add(c5);
    assert(ret == AM_OK);
    assert(solver->rows.count == 7);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 5.0);
    assert(am_value(xr) == 10.0);
    am_remove(c5);
    assert(solver->rows.count == 6);

    c5 = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c5, xl, 1.0);
    am_setrelation(c5, AM_EQUAL);
    am_addconstant(c5, 0.0);
    ret = am_add(c5);
    assert(ret == AM_OK);
    assert(solver->rows.count == 7);

    c6 = am_cloneconstraint(c4, AM_REQUIRED);
    ret = am_add(c6);
    assert(ret == AM_OK);
    am_updatevars(solver);
    assert(solver->rows.count == 8);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 5.0);
    assert(am_value(xr) == 10.0);

    am_resetconstraint(c6);
    am_delconstraint(c6);

    am_remove(c1);
    am_remove(c2);
    am_remove(c3);
    am_remove(c4);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 4.0);
    assert(am_value(xr) == 2.0);
    ret |= am_add(c4);
    ret |= am_add(c3);
    ret |= am_add(c2);
    ret |= am_add(c1);
    assert(ret == AM_OK);

    am_resetsolver(solver, 0);
    am_resetsolver(solver, 1);
    assert(solver->rows.count == 0);
    ret |= am_add(c1);
    ret |= am_add(c2);
    ret |= am_add(c3);
    ret |= am_add(c4);
    assert(ret == AM_OK);

    am_updatevars(solver);
    assert(am_value(xl) == 90.0);
    assert(am_value(xm) == 95.0);
    assert(am_value(xr) == 100.0);

    am_addedit(xm, AM_MEDIUM);
    am_updatevars(solver);
    assert(am_value(xl) == 90.0);
    assert(am_value(xm) == 95.0);
    assert(am_value(xr) == 100.0);

    assert(am_hasedit(xm));

    am_suggest(xm, 0.0);
    am_updatevars(solver);
    assert(am_value(xl) == 0.0);
    assert(am_value(xm) == 5.0);
    assert(am_value(xr) == 10.0);

    am_suggest(xm, 70.0);
    am_updatevars(solver);
    assert(am_value(xl) == 40.0);
    assert(am_value(xm) == 70.0);
    assert(am_value(xr) == 100.0);

    am_deledit(xm);
    am_updatevars(solver);
    assert(am_value(xl) == 90.0);
    assert(am_value(xm) == 95.0);
    assert(am_value(xr) == 100.0);

    am_delsolver(solver);
    assert(maxmem == 11728);
    assert(allmem == 0);
    maxmem = 0;
    printf("test_all passed\n");
}

static void test_binarytree()
{
    printf("test_binarytree...\n");
    /* Create set of rules to distribute vertexes of a binary tree like this
     * one:
     *      0
     *     / \
     *    /   \
     *   1     2
     *  / \   / \
     * 3   4 5   6
     */

    const int NUM_ROWS = 9;
    int num_variables = 1 << (NUM_ROWS + 1);
    am_Variable **arrX =
        (am_Variable **)malloc(num_variables * sizeof(am_Variable *));
    if (arrX == NULL)
        return;
    am_Variable **arrY = arrX + (1 << NUM_ROWS);

    am_Solver *pSolver = am_newsolver(debug_allocf, NULL);

    arrX[0] = am_newvariable(pSolver);
    arrY[0] = am_newvariable(pSolver);
    am_addedit(arrX[0], AM_STRONG);
    am_addedit(arrY[0], AM_STRONG);
    am_suggest(arrX[0], 500.0f);
    am_suggest(arrY[0], 10.0f);

    int nCurrentRowPointsCount = 1;
    int nCurrentRowFirstPointIndex = 0;
    int nResult;
    am_Constraint *pC;
    for (int nRow = 1; nRow < NUM_ROWS; nRow++) {
        int nPreviousRowFirstPointIndex = nCurrentRowFirstPointIndex;
        int nParentPoint = 0;
        nCurrentRowFirstPointIndex += nCurrentRowPointsCount;
        nCurrentRowPointsCount *= 2;

        for (int nPoint = 0; nPoint < nCurrentRowPointsCount; nPoint++) {
            arrX[nCurrentRowFirstPointIndex + nPoint] = am_newvariable(pSolver);
            arrY[nCurrentRowFirstPointIndex + nPoint] = am_newvariable(pSolver);

            /* Ycur = Yprev_row + 15 */
            pC = am_newconstraint(pSolver, AM_REQUIRED);
            am_addterm(pC, arrY[nCurrentRowFirstPointIndex + nPoint], 1.0);
            am_setrelation(pC, AM_EQUAL);
            am_addterm(pC, arrY[nCurrentRowFirstPointIndex - 1], 1.0);
            am_addconstant(pC, 15.0);
            nResult = am_add(pC);
            assert(nResult == AM_OK);

            if (nPoint > 0) {
                /* Xcur >= XPrev + 5 */
                pC = am_newconstraint(pSolver, AM_REQUIRED);
                am_addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
                am_setrelation(pC, AM_GREATEQUAL);
                am_addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1],
                           1.0);
                am_addconstant(pC, 5.0);
                nResult = am_add(pC);
                assert(nResult == AM_OK);
            }
            else {
                /* Xcur >= 0 */
                pC = am_newconstraint(pSolver, AM_REQUIRED);
                am_addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
                am_setrelation(pC, AM_GREATEQUAL);
                am_addconstant(pC, 0.0);
                nResult = am_add(pC);
                assert(nResult == AM_OK);
            }

            if ((nPoint % 2) == 1) {
                /* Xparent = 0.5 * Xcur + 0.5 * Xprev */
                pC = am_newconstraint(pSolver, AM_REQUIRED);
                am_addterm(pC, arrX[nPreviousRowFirstPointIndex + nParentPoint],
                           1.0);
                am_setrelation(pC, AM_EQUAL);
                am_addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 0.5);
                am_addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1],
                           0.5);
                nResult = am_add(pC);
                assert(nResult == AM_OK);

                nParentPoint++;
            }
        }
    }
    am_updatevars(pSolver);
    int nPointsCount = nCurrentRowFirstPointIndex + nCurrentRowPointsCount;

#include "expected_binary_tree_values.h"
    for (int i = 0; i < nPointsCount; ++i) {
        assert(abs(expected_binary_tree_values[2 * i] - am_value(arrX[i])) <
               0.1);
        assert(abs(expected_binary_tree_values[2 * i + 1] - am_value(arrY[i])) <
               0.1);
    }

    am_delsolver(pSolver);
    assert(maxmem == 3652176);
    assert(allmem == 0);
    free(arrX);
    maxmem = 0;
    printf("test_binarytree passed\n");
}

static void test_unbounded()
{
    printf("test_unbounded...\n");
    am_Solver *solver;
    am_Variable *x, *y;
    am_Constraint *c;
    int ret = setjmp(jbuf);
    if (ret < 0) {
        perror("setjmp");
        return;
    }
    else if (ret != 0) {
        printf("out of memory!\n");
        return;
    }

    solver = am_newsolver(debug_allocf, NULL);
    x = am_newvariable(solver);
    y = am_newvariable(solver);

    /* 10.0 == 0.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addconstant(c, 10.0);
    am_setrelation(c, AM_EQUAL);
    ret = am_add(c);
    assert(ret == AM_UNSATISFIED);
    assert(solver->rows.count == 0);

    /* 0.0 == 0.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addconstant(c, 0.0);
    am_setrelation(c, AM_EQUAL);
    ret = am_add(c);
    assert(ret == AM_OK);
    assert(solver->rows.count == 1);

    am_resetsolver(solver, 1);

    /* x >= 10.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_GREATEQUAL);
    am_addconstant(c, 10.0);
    ret = am_add(c);
    assert(ret == AM_OK);
    assert(solver->rows.count == 1);
    am_updatevars(solver);
    assert(am_value(x) == 10.0);

    /* x == 2*y */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_EQUAL);
    am_addterm(c, y, 2.0);
    ret = am_add(c);
    assert(ret == AM_OK);
    assert(solver->rows.count == 2);
    am_updatevars(solver);
    assert(am_value(x) == 10.0);
    assert(am_value(y) == 5.0);

    /* y == 3*x */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, y, 1.0);
    am_setrelation(c, AM_EQUAL);
    am_addterm(c, x, 3.0);
    ret = am_add(c);
    assert(ret == AM_UNBOUND);
    assert(solver->rows.count == 2);
    am_updatevars(solver);

    am_resetsolver(solver, 1);
    assert(solver->rows.count == 0);

    /* x >= 10.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_GREATEQUAL);
    am_addconstant(c, 10.0);
    ret = am_add(c);
    assert(solver->rows.count == 1);
    assert(ret == AM_OK);
    am_updatevars(solver);
    assert(am_value(x) == 10.0);

    /* x <= 0.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_LESSEQUAL);
    ret = am_add(c);
    assert(solver->rows.count == 1);
    assert(ret == AM_UNBOUND);

    am_resetsolver(solver, 1);
    assert(solver->rows.count == 0);

    /* x == 10.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_EQUAL);
    am_addconstant(c, 10.0);
    ret = am_add(c);
    assert(solver->rows.count == 1);
    assert(ret == AM_OK);

    /* x == 20.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_EQUAL);
    am_addconstant(c, 20.0);
    ret = am_add(c);
    assert(ret == AM_UNSATISFIED);
    assert(solver->rows.count == 1);

    /* x == 10.0 */
    c = am_newconstraint(solver, AM_REQUIRED);
    am_addterm(c, x, 1.0);
    am_setrelation(c, AM_EQUAL);
    am_addconstant(c, 10.0);
    ret = am_add(c);
    assert(ret == AM_OK);
    assert(solver->rows.count == 2);

    am_delsolver(solver);
    assert(maxmem == 9680);
    assert(allmem == 0);
    maxmem = 0;
    printf("test_unbounded passed\n");
}

static void test_strength()
{
    printf("test_strength...\n");
    am_Solver *solver;
    am_Variable *x, *y;
    am_Constraint *c;
    int ret = setjmp(jbuf);
    if (ret < 0) {
        perror("setjmp");
        return;
    }
    else if (ret != 0) {
        printf("out of memory!\n");
        return;
    }

    solver = am_newsolver(debug_allocf, NULL);
    am_autoupdate(solver, 1);
    x = am_newvariable(solver);
    y = am_newvariable(solver);

    /* x <= y */
    new_constraint(solver, AM_STRONG, x, 1.0, AM_LESSEQUAL, 0.0, y, 1.0, END);
    new_constraint(solver, AM_MEDIUM, x, 1.0, AM_EQUAL, 50, END);
    c = new_constraint(solver, AM_MEDIUM - 10, y, 1.0, AM_EQUAL, 40, END);
    assert(am_value(x) == 50);
    assert(am_value(y) == 50);

    am_setstrength(c, AM_MEDIUM + 10);
    assert(am_value(x) == 40);
    assert(am_value(y) == 40);

    am_setstrength(c, AM_MEDIUM - 10);
    assert(am_value(x) == 50);
    assert(am_value(y) == 50);

    am_delsolver(solver);
    assert(maxmem == 9616);
    assert(allmem == 0);
    maxmem = 0;
    printf("test_strength passed\n");
}

static void test_suggest()
{
    printf("test_suggest...\n");
#if 1
    am_Float strength1 = AM_REQUIRED;
    am_Float strength2 = AM_REQUIRED;
    size_t expected_maxmem = 12048;
#else
    am_Float strength1 = AM_STRONG;
    am_Float strength2 = AM_WEAK;
    size_t expected_maxmem = 12112;
#endif
    am_Float delta = 0;
    am_Float pos;
    am_Solver *solver;
    am_Variable *splitter_l, *splitter_w, *splitter_r;
    am_Variable *left_child_l, *left_child_w, *left_child_r;
    am_Variable *splitter_bar_l, *splitter_bar_w, *splitter_bar_r;
    am_Variable *right_child_l, *right_child_w, *right_child_r;
    int ret = setjmp(jbuf);
    if (ret < 0) {
        perror("setjmp");
        return;
    }
    else if (ret != 0) {
        printf("out of memory!\n");
        return;
    }

    solver = am_newsolver(debug_allocf, NULL);
    splitter_l = am_newvariable(solver);
    splitter_w = am_newvariable(solver);
    splitter_r = am_newvariable(solver);
    left_child_l = am_newvariable(solver);
    left_child_w = am_newvariable(solver);
    left_child_r = am_newvariable(solver);
    splitter_bar_l = am_newvariable(solver);
    splitter_bar_w = am_newvariable(solver);
    splitter_bar_r = am_newvariable(solver);
    right_child_l = am_newvariable(solver);
    right_child_w = am_newvariable(solver);
    right_child_r = am_newvariable(solver);

    /* splitter_r = splitter_l + splitter_w */
    /* left_child_r = left_child_l + left_child_w */
    /* splitter_bar_r = splitter_bar_l + splitter_bar_w */
    /* right_child_r = right_child_l + right_child_w */
    new_constraint(solver, AM_REQUIRED, splitter_r, 1.0, AM_EQUAL, 0.0,
                   splitter_l, 1.0, splitter_w, 1.0, END);
    new_constraint(solver, AM_REQUIRED, left_child_r, 1.0, AM_EQUAL, 0.0,
                   left_child_l, 1.0, left_child_w, 1.0, END);
    new_constraint(solver, AM_REQUIRED, splitter_bar_r, 1.0, AM_EQUAL, 0.0,
                   splitter_bar_l, 1.0, splitter_bar_w, 1.0, END);
    new_constraint(solver, AM_REQUIRED, right_child_r, 1.0, AM_EQUAL, 0.0,
                   right_child_l, 1.0, right_child_w, 1.0, END);

    /* splitter_bar_w = 6 */
    /* splitter_bar_l >= splitter_l + delta */
    /* splitter_bar_r <= splitter_r - delta */
    /* left_child_r = splitter_bar_l */
    /* right_child_l = splitter_bar_r */
    new_constraint(solver, AM_REQUIRED, splitter_bar_w, 1.0, AM_EQUAL, 6.0,
                   END);
    new_constraint(solver, AM_REQUIRED, splitter_bar_l, 1.0, AM_GREATEQUAL,
                   delta, splitter_l, 1.0, END);
    new_constraint(solver, AM_REQUIRED, splitter_bar_r, 1.0, AM_LESSEQUAL,
                   -delta, splitter_r, 1.0, END);
    new_constraint(solver, AM_REQUIRED, left_child_r, 1.0, AM_EQUAL, 0.0,
                   splitter_bar_l, 1.0, END);
    new_constraint(solver, AM_REQUIRED, right_child_l, 1.0, AM_EQUAL, 0.0,
                   splitter_bar_r, 1.0, END);

    /* right_child_r >= splitter_r + 1 */
    /* left_child_w = 256 */
    new_constraint(solver, strength1, right_child_r, 1.0, AM_GREATEQUAL, 1.0,
                   splitter_r, 1.0, END);
    new_constraint(solver, strength2, left_child_w, 1.0, AM_EQUAL, 256.0, END);

#include "expected_splitter_values.h"
    int exptected_index = 0;
    for (pos = -10; pos < 50; pos += 10) {
        am_suggest(splitter_bar_l, pos);
        am_updatevars(solver);
        assert(am_value(splitter_l) ==
               expected_splitter_values[exptected_index][0]);
        assert(am_value(splitter_w) ==
               expected_splitter_values[exptected_index][1]);
        assert(am_value(splitter_r) ==
               expected_splitter_values[exptected_index][2]);
        assert(am_value(left_child_l) ==
               expected_splitter_values[exptected_index][3]);
        assert(am_value(left_child_w) ==
               expected_splitter_values[exptected_index][4]);
        assert(am_value(left_child_r) ==
               expected_splitter_values[exptected_index][5]);
        assert(am_value(splitter_bar_l) ==
               expected_splitter_values[exptected_index][6]);
        assert(am_value(splitter_bar_w) ==
               expected_splitter_values[exptected_index][7]);
        assert(am_value(splitter_bar_r) ==
               expected_splitter_values[exptected_index][8]);
        assert(am_value(right_child_l) ==
               expected_splitter_values[exptected_index][9]);
        assert(am_value(right_child_w) ==
               expected_splitter_values[exptected_index][10]);
        assert(am_value(right_child_r) ==
               expected_splitter_values[exptected_index][11]);
        ++exptected_index;
    }

    am_autoupdate(solver, 1);

    for (pos = 60; pos < 86; pos += 10) {
        am_suggest(splitter_bar_l, pos);
        assert(am_value(splitter_l) ==
               expected_splitter_values[exptected_index][0]);
        assert(am_value(splitter_w) ==
               expected_splitter_values[exptected_index][1]);
        assert(am_value(splitter_r) ==
               expected_splitter_values[exptected_index][2]);
        assert(am_value(left_child_l) ==
               expected_splitter_values[exptected_index][3]);
        assert(am_value(left_child_w) ==
               expected_splitter_values[exptected_index][4]);
        assert(am_value(left_child_r) ==
               expected_splitter_values[exptected_index][5]);
        assert(am_value(splitter_bar_l) ==
               expected_splitter_values[exptected_index][6]);
        assert(am_value(splitter_bar_w) ==
               expected_splitter_values[exptected_index][7]);
        assert(am_value(splitter_bar_r) ==
               expected_splitter_values[exptected_index][8]);
        assert(am_value(right_child_l) ==
               expected_splitter_values[exptected_index][9]);
        assert(am_value(right_child_w) ==
               expected_splitter_values[exptected_index][10]);
        assert(am_value(right_child_r) ==
               expected_splitter_values[exptected_index][11]);
        ++exptected_index;
    }

    am_delsolver(solver);
    assert(allmem == 0);
    assert(maxmem == expected_maxmem);
    maxmem = 0;
    printf("test_suggest passed\n");
}

void test_cycling()
{
    printf("test_cycling...\n");
    am_Solver *solver = am_newsolver(debug_allocf, NULL);

    am_Variable *va = am_newvariable(solver);
    am_Variable *vb = am_newvariable(solver);
    am_Variable *vc = am_newvariable(solver);
    am_Variable *vd = am_newvariable(solver);

    am_addedit(va, AM_STRONG);
    assert(solver->rows.count == 1);

    /* vb == va */
    {
        am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
        int ret = 0;
        ret |= am_addterm(c, vb, 1.0);
        ret |= am_setrelation(c, AM_EQUAL);
        ret |= am_addterm(c, va, 1.0);
        ret |= am_add(c);
        assert(ret == AM_OK);
        assert(solver->rows.count == 2);
        am_suggest(va, 1.5);
        am_updatevars(solver);
        assert(am_value(va) == 1.5);
        assert(am_value(vb) == 1.5);
    }

    /* vb == vc */
    {
        am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
        int ret = 0;
        ret |= am_addterm(c, vb, 1.0);
        ret |= am_setrelation(c, AM_EQUAL);
        ret |= am_addterm(c, vc, 1.0);
        ret |= am_add(c);
        assert(ret == AM_OK);
        assert(solver->rows.count == 3);
        am_updatevars(solver);
        assert(am_value(vb) == 1.5);
        assert(am_value(vc) == 1.5);
    }

    /* vc == vd */
    {
        am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
        int ret = 0;
        ret |= am_addterm(c, vc, 1.0);
        ret |= am_setrelation(c, AM_EQUAL);
        ret |= am_addterm(c, vd, 1.0);
        ret |= am_add(c);
        assert(ret == AM_OK);
        assert(solver->rows.count == 4);
        am_updatevars(solver);
        assert(am_value(vb) == 1.5);
        assert(am_value(vd) == 1.5);
    }

    /* vd == va */
    {
        am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
        int ret = 0;
        ret |= am_addterm(c, vd, 1.0);
        ret |= am_setrelation(c, AM_EQUAL);
        ret |= am_addterm(c, va, 1.0);
        ret |= am_add(c);
        assert(ret == AM_OK);
        assert(solver->rows.count == 5);
        am_updatevars(solver);
        assert(am_value(vd) == 1.5);
        assert(am_value(va) == 1.5);
    }

    am_delsolver(solver);
    assert(allmem == 0);
    assert(maxmem == 10320);
    maxmem = 0;
    printf("test_cycling passed\n");
}

void test_set_strength()
{
    printf("test_set_strength...\n");
    am_Solver *solver = am_newsolver(NULL, NULL);
    am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
    int ret = am_setstrength(c, AM_REQUIRED);
    assert(ret == AM_OK);

    ret = am_setstrength(c, 0.0);
    assert(ret == AM_OK);
    assert(c->strength == AM_REQUIRED);

    ret = am_setstrength(c, 11000);
    assert(ret == AM_OK);
    assert(c->strength == 11000);
    printf("test_set_strength passed\n");
}

void test_null()
{
    printf("test_null...\n");
    int ret = 0;
    am_resetconstraint(NULL);
    am_deledit(NULL);
    am_suggest(NULL, 0.0);
    am_addedit(NULL, 0.0);
    am_setstrength(NULL, 0.0);

    am_Constraint *c0 = am_cloneconstraint(NULL, 0.0);
    assert(c0 == NULL);

    ret = am_mergeconstraint(NULL, NULL, 0.0);
    assert(ret == AM_FAILED);

    am_Solver *solver = am_newsolver(NULL, NULL);
    am_Constraint *c = am_newconstraint(solver, AM_REQUIRED);
    ret = am_mergeconstraint(c, NULL, 0.0);
    assert(ret == AM_FAILED);

    am_Solver *solver2 = am_newsolver(NULL, NULL);
    am_Constraint *c2 = am_newconstraint(solver2, AM_REQUIRED);
    assert(c->marker.id == 0);
    assert(c->solver != c2->solver);
    ret = am_mergeconstraint(c, c2, 0.0);
    assert(ret == AM_FAILED);
    printf("test_null passed\n");
}

int main()
{
    test_all();
    test_null();
    test_set_strength();
    test_cycling();
    test_suggest();
    test_binarytree();
    test_strength();
    test_unbounded();

    (void)am_dumpsolver(NULL);
    return 0;
}
