#ifndef amoeba_h
#define amoeba_h

#ifndef AM_NS_BEGIN
#ifdef __cplusplus
#define AM_NS_BEGIN extern "C" {
#define AM_NS_END }
#else
#define AM_NS_BEGIN
#define AM_NS_END
#endif
#endif /* AM_NS_BEGIN */

#ifndef AM_STATIC
#ifdef __GNUC__
#define AM_STATIC static __attribute((unused))
#else
#define AM_STATIC static
#endif
#endif

#ifdef AM_STATIC_API
#ifndef AM_IMPLEMENTATION
#define AM_IMPLEMENTATION
#endif
#define AM_API AM_STATIC
#endif

#if !defined(AM_API) && defined(_WIN32)
#ifdef AM_IMPLEMENTATION
#define AM_API __declspec(dllexport)
#else
#define AM_API __declspec(dllimport)
#endif
#endif

#ifndef AM_API
#define AM_API extern
#endif

#define AM_OK (0)
#define AM_FAILED (-1)
#define AM_UNSATISFIED (-2)
#define AM_UNBOUND (-3)

#define AM_LESSEQUAL (1)
#define AM_EQUAL (2)
#define AM_GREATEQUAL (3)

#define AM_REQUIRED ((am_Float)1000000000)
#define AM_STRONG ((am_Float)1000000)
#define AM_MEDIUM ((am_Float)1000)
#define AM_WEAK ((am_Float)1)

#include <stddef.h>

AM_NS_BEGIN

#ifdef AM_USE_FLOAT
typedef float am_Float;
#else
typedef double am_Float;
#endif

typedef struct am_Solver am_Solver;
typedef struct am_Variable am_Variable;
typedef struct am_Constraint am_Constraint;

typedef void *am_Allocf(void *ud, void *ptr, size_t nsize, size_t osize);

AM_API am_Solver *am_newsolver(am_Allocf *allocf, void *ud);
AM_API void am_resetsolver(am_Solver *solver, int clear_constraints);
AM_API void am_delsolver(am_Solver *solver);

AM_API void am_updatevars(am_Solver *solver);
AM_API void am_autoupdate(am_Solver *solver, int auto_update);

AM_API int am_hasedit(am_Variable *var);
AM_API int am_hasconstraint(am_Constraint *cons);

AM_API int am_add(am_Constraint *cons);
AM_API void am_remove(am_Constraint *cons);

AM_API int am_addedit(am_Variable *var, am_Float strength);
AM_API void am_suggest(am_Variable *var, am_Float value);
AM_API void am_deledit(am_Variable *var);

AM_API am_Variable *am_newvariable(am_Solver *solver);
AM_API void am_usevariable(am_Variable *var);
AM_API void am_delvariable(am_Variable *var);
AM_API int am_variableid(am_Variable *var);
AM_API am_Float am_value(am_Variable *var);

AM_API am_Constraint *am_newconstraint(am_Solver *solver, am_Float strength);
AM_API am_Constraint *am_cloneconstraint(am_Constraint *other,
                                         am_Float strength);

AM_API void am_resetconstraint(am_Constraint *cons);
AM_API void am_delconstraint(am_Constraint *cons);

AM_API int am_addterm(am_Constraint *cons, am_Variable *var,
                      am_Float multiplier);
AM_API int am_setrelation(am_Constraint *cons, int relation);
AM_API int am_addconstant(am_Constraint *cons, am_Float constant);
AM_API int am_setstrength(am_Constraint *cons, am_Float strength);

AM_API int am_mergeconstraint(am_Constraint *cons, am_Constraint *other,
                              am_Float multiplier);

AM_NS_END

#endif /* amoeba_h */
