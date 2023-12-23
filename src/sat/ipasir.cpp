/* Part of the generic incremental SAT API called 'ipasir'.
 * See 'LICENSE' for rights to use this software.
 */

/*
 * In this header, the macro IPASIR_API is defined as follows:
 * - if IPASIR_SHARED_LIB is not defined, then IPASIR_API is defined, but empty.
 * - if IPASIR_SHARED_LIB is defined...
 *    - ...and if BUILDING_IPASIR_SHARED_LIB is not defined, IPASIR_API is
 *      defined to contain symbol visibility attributes for importing symbols
 *      of a DSO (including the __declspec rsp. __attribute__ keywords).
 *    - ...and if BUILDING_IPASIR_SHARED_LIB is defined, IPASIR_API is defined
 *      to contain symbol visibility attributes for exporting symbols from a
 *      DSO (including the __declspec rsp. __attribute__ keywords).
 */

#if defined(IPASIR_SHARED_LIB)
    #if defined(_WIN32) || defined(__CYGWIN__)
        #if defined(BUILDING_IPASIR_SHARED_LIB)
            #if defined(__GNUC__)
                #define IPASIR_API __attribute__((dllexport))
            #elif defined(_MSC_VER)
                #define IPASIR_API __declspec(dllexport)
            #endif
        #else
            #if defined(__GNUC__)
                #define IPASIR_API __attribute__((dllimport))
            #elif defined(_MSC_VER)
                #define IPASIR_API __declspec(dllimport)
            #endif
        #endif
    #elif defined(__GNUC__)
        #define IPASIR_API __attribute__((visibility("default")))
    #endif

    #if !defined(IPASIR_API)
        #if !defined(IPASIR_SUPPRESS_WARNINGS)
            #warning "Unknown compiler. Not adding visibility information to IPASIR symbols."
            #warning "Define IPASIR_SUPPRESS_WARNINGS to suppress this warning."
        #endif
        #define IPASIR_API
    #endif
#else
    #define IPASIR_API
#endif

//#ifdef __cplusplus
//extern "C" {
//#endif



#include "ipasir.h"
#include <cvc5/cvc5.h>
#include <iostream>
#include <numeric>
#include <vector>
#include "../flags.h" // defines flags

#include "partial_order.h"
#include "../Model.h"
//#include "pdt.h"
#include "sog.h"

using namespace cvc5;

Sort boolSort;
std::vector<Term> terms;
int tsize = 128;
bool firstloop = true;
std::vector<Term> ors;

Sort intSort;
std::vector<Term> rleafs;
std::vector<Term> rleaftasks;
std::vector<Term> rpostasks;
Term zero;
Term nPositions;
//rleafs.resize(leafSOG->numberOfVertices);


/**
 * Return the name and the version of the incremental SAT
 * solving library.
 */
IPASIR_API const char * ipasir_signature (){
    return "cvc bool";
}
/**
 * Construct a new solver and return a pointer to it.
 * Use the returned pointer as the first parameter in each
 * of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
IPASIR_API void * ipasir_init (){
    std::cerr << "init";
    Solver *solver = new Solver();
    solver->setOption("produce-models", "true");
    solver->setOption("produce-unsat-cores", "true");
    boolSort = solver->getBooleanSort();
    intSort = solver->getIntegerSort();

    if (firstloop){
        terms.resize(tsize);
        for (int i = 0; i < tsize; i++)
            terms[i] = solver->mkConst(boolSort, std::to_string(i));
        firstloop = false;
    }
    return solver;
}

/**
 * Release the solver, i.e., all its resoruces and
 * allocated memory (destructor). The solver pointer
 * cannot be used for any purposes after this call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: undefined
 */
IPASIR_API void ipasir_release (void * solver){
    std::cerr << "rel";
    Solver *s = (Solver*)solver;
    std::cerr << "rel2";

    delete s;
    std::cerr << "rel3";
    return;
}

/**
 * Add the given literal into the currently added clause
 * or finalize the clause with a 0.  Clauses added this way
 * cannot be removed. The addition of removable clauses
 * can be simulated using activation literals and assumptions.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 *
 * Literals are encoded as (non-zero) integers as in the
 * DIMACS formats.  They have to be smaller or equal to
 * INT_MAX and strictly larger than INT_MIN (to avoid
 * negation overflow).  This applies to all the literal
 * arguments in API functions.
 */
IPASIR_API void ipasir_add (void * solver, int lit_or_zero){
    //std::cerr << "add";
    //std::cerr << lit_or_zero;
    Solver *s = (Solver*)solver;
    if (lit_or_zero != 0){
        int i = abs(lit_or_zero);
        while (i > tsize){
            terms.resize(tsize*2);
            for (int j = tsize; j < tsize*2; j++){
                terms[j] = s->mkConst(boolSort, std::to_string(j));
            }
            tsize = tsize*2;
        }
        if (lit_or_zero < 0)
            ors.push_back(s->mkTerm(cvc5::Kind::NOT, {terms[i-1]}));
        else
            ors.push_back(terms[i-1]);
    } else {
        if (ors.size() == 1)
            s->assertFormula(ors[0]);
        else {
            Term constraint = s->mkTerm(cvc5::Kind::OR, ors);
            s->assertFormula(constraint);
        }
        ors.clear();
    }

    return;
}

/**
 * Add an assumption for the next SAT search (the next call
 * of ipasir_solve). After calling ipasir_solve all the
 * previously added assumptions are cleared.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 */
IPASIR_API void ipasir_assume (void * solver, int lit);

/**
 * Solve the formula with specified clauses under the specified assumptions.
 * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
 * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
 * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
 * This function can be called in any defined state of the solver.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
IPASIR_API int ipasir_solve (void * solver){
    std::cerr << "sol";
    Solver *s = (Solver*)solver;
    Result r1 = s->checkSat();
    if(r1.isSat()){
        for(const Term& t :rleafs){
            std::cout << t;
            std::cout << ": ";
            std::cout << s->getValue(t) << std::endl;
        }
        for(const Term& t :rleaftasks){
            std::cout << t;
            std::cout << ": ";
            std::cout << s->getValue(t) << std::endl;
        }
        for(const Term& t :rpostasks){
            std::cout << t;
            std::cout << ": ";
            std::cout << s->getValue(t) << std::endl;
        }
        return 10;
    }
    if (r1.isUnsat()){
        std::vector<Term> unsatCore = s->getUnsatCore();
        std::cout << "unsat core size: " << unsatCore.size() << std::endl;
        std::cout << "unsat core: " << std::endl;
        for (const Term& t : unsatCore){
            std::cout << t << std::endl;
        }
        return 20;
    }
    return 0;
}

/**
 * Get the truth value of the given literal in the found satisfying
 * assignment. Return 'lit' if True, '-lit' if False, and 0 if not important.
 * This function can only be used if ipasir_solve has returned 10
 * and no 'ipasir_add' nor 'ipasir_assume' has been called
 * since then, i.e., the state of the solver is SAT.
 *
 * Required state: SAT
 * State after: SAT
 */
IPASIR_API int ipasir_val (void * solver, int lit){
    Solver *s = (Solver*)solver;
    if(s->getValue(terms[lit-1]).getBooleanValue())
        return lit;
    return -lit;
}
/**
 * Check if the given assumption literal was used to prove the
 * unsatisfiability of the formula under the assumptions
 * used for the last SAT search. Return 1 if so, 0 otherwise.
 * This function can only be used if ipasir_solve has returned 20 and
 * no ipasir_add or ipasir_assume has been called since then, i.e.,
 * the state of the solver is UNSAT.
 *
 * Required state: UNSAT
 * State after: UNSAT
 */
IPASIR_API int ipasir_failed (void * solver, int lit);

/**
 * Set a callback function used to indicate a termination requirement to the
 * solver. The solver will periodically call this function and check its return
 * value during the search. The ipasir_set_terminate function can be called in any
 * state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "int terminate(void * state)"
 *   - it returns a non-zero value if the solver should terminate.
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipasir_set_terminate function (2nd parameter).
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
IPASIR_API void ipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state));

/**
 * Set a callback function used to extract learned clauses up to a given length from the
 * solver. The solver will call this function for each learned clause that satisfies
 * the maximum length (literal count) condition. The ipasir_set_learn function can be called in any
 * state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "void learn(void * state, int * clause)"
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipasir_set_learn function (2nd parameter).
 *   - the argument "clause" is a pointer to a null terminated integer array containing the learned clause.
 *     the solver can change the data at the memory location that "clause" points to after the function call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
IPASIR_API void ipasir_set_learn (void * solver, void * state, int max_length, void (*learn)(void * state, int * clause));

void ipasir_init_reals(void * solver, int numVertices, int numPositions){
    // initiate integer term for tracking position each leaf is at
    // constrain each leaf to be less than number of positions and all to be distinct
    // l terms, l constraints
    Solver *s = (Solver*)solver;
    std::cout << "rls";
    std::cout << numVertices;
    zero = s->mkInteger(0);
    nPositions = s->mkInteger(numPositions);
    rleafs.resize(numVertices);
 	for (int l = 0; l < numVertices; l++){
        Term a = s->mkConst(intSort, "leaf" + std::to_string(l));
        rleafs[l] = a;
        Term constraint = s->mkTerm(cvc5::Kind::LT, {a, nPositions});
        s->assertFormula(constraint);
    }
    Term constraint = s->mkTerm(cvc5::Kind::DISTINCT, rleafs);
    s->assertFormula(constraint);
}

void ipasir_init_leaf_tasks(void * solver, int numVertices){
    Solver *s = (Solver*)solver;
    rleaftasks.resize(numVertices);
/*    for (int l = 0; l < numVertices; l++){
        Term a = s->mkConst(intSort, "leaft" + std::to_string(l));
        rleaftasks[l] = a;
        PDT * leaf = leafSOG->leafOfNode[l];
        std::vector<Term> constraints;
        for (int prim = 0; prim < leaf->possiblePrimitives.size(); prim++){
            if (leaf->primitiveVariable[prim] == -1) continue; // pruned
            Term primt = s->mkInteger(leaf->possiblePrimitives[prim]);
            constraints.push_back(s->mkTerm(cvc5::Kind::EQUAL, {a, primt}));
        }
        constraints.push_back(s->mkTerm(cvc5::Kind::LT, {a, zero}));
        Term constraint = s->mkTerm(cvc5::Kind::OR, constraints);
        s->assertFormula(constraint);
    }*/
}

void ipasir_init_leaf_task(void * solver, int l, PDT * leaf){
    // initiate integer term for tracking the task each leaf performs
    // constrain each leaf to only do tasks it can perform
    // also turn on the appropriate boolean primitive for leaf/task pairs
    // l terms, at most 2*l*t constraints
    Solver *s = (Solver*)solver;
    Term a = s->mkConst(intSort, "leaft" + std::to_string(l));
    cout << a;
    rleaftasks[l] = a;
    //PDT * leaf = leafSOG->leafOfNode[l];
    if (leaf->possiblePrimitives.size() == 0) {
        Term constraint = (s->mkTerm(cvc5::Kind::LT, {a, zero}));
        s->assertFormula(constraint);
        return;
    }
    std::vector<Term> constraints;
    for (int prim = 0; prim < leaf->possiblePrimitives.size(); prim++){
        if (leaf->primitiveVariable[prim] == -1) continue; // pruned
        Term primt = s->mkInteger(leaf->possiblePrimitives[prim]);
        Term leaftask = s->mkTerm(cvc5::Kind::EQUAL, {a, primt});
        int b = leaf->primitiveVariable[prim];
        Term c = s->mkTerm(cvc5::Kind::EQUAL, {leaftask, terms[b-1]});
        s->assertFormula(c);
        constraints.push_back(leaftask);
    }
    constraints.push_back(s->mkTerm(cvc5::Kind::LT, {a, zero}));
    Term constraint = s->mkTerm(cvc5::Kind::OR, constraints);
    s->assertFormula(constraint);
}

void ipasir_init_position_tasks(void * solver, int numVertices, int numPositions){
    // initiate integer terms for tracking tasks performed at each position
    // constrain each position to perform the task performed by the leaf at that position
    // p terms, l x p constraints
    Solver *s = (Solver*)solver;
    rpostasks.resize(numPositions);
    cout << "rl??";
    cout << rleafs.size();
    cerr << "\nrlt???";
    cerr << rleaftasks.size();

    for(int p = 0; p < numPositions; p++){
        Term pos = s->mkInteger(p);
        Term a = s->mkConst(intSort, "pos" + std::to_string(p));
        rpostasks[p] = a;
        std::vector<Term> constraints;
        for(int l = 0; l < numVertices; l++){
            Term c1 = s->mkTerm(cvc5::Kind::EQUAL, {rleafs[l], pos});
            Term c2 = s->mkTerm(cvc5::Kind::EQUAL, {rleaftasks[l], a});
            Term c3 = s->mkTerm(cvc5::Kind::IMPLIES, {c1, c2});
            s->assertFormula(c3);
            constraints.push_back(c1);
        }
        constraints.push_back(s->mkTerm(cvc5::Kind::LT, {a, zero}));
        Term constraint = s->mkTerm(cvc5::Kind::OR, constraints);
        s->assertFormula(constraint);
    }
}

void ipasir_constrain_task_positions(void * solver, int task, int position, int b){
    // if task t is done at position p turn on the primitive boolean
    // t x p constraints
    Solver *s = (Solver*)solver;
    Term t = s->mkInteger(task);
    Term c1 = s->mkTerm(cvc5::Kind::EQUAL, {rpostasks[position], t});
    Term c2 = s->mkTerm(cvc5::Kind::EQUAL, {c1, terms[b-1]});
    s->assertFormula(c2);
}

void ipasir_reals_successor(void * solver, int leaf, int succ){
    // if a leaf has an active successor, then it must be at an earlier position than the successor
    // at most l x l constraints
    Solver *s = (Solver*)solver;
    Term constraint1 = s->mkTerm(cvc5::Kind::LEQ, {zero, rleafs[succ]});
    Term constraint2 = s->mkTerm(cvc5::Kind::LT, {rleafs[leaf], rleafs[succ]});
    Term constraint3 = s->mkTerm(cvc5::Kind::IMPLIES, {constraint1, constraint2});
    s->assertFormula(constraint3);
}

void ipasir_reals_active(void * solver, int leaf, int b){
    // leafs have tasks iff they have positions
    // l constraints
    Solver *s = (Solver*)solver;
    Term constraint1 = s->mkTerm(cvc5::Kind::LEQ, {zero, rleafs[leaf]});
    Term constraint2 = s->mkTerm(cvc5::Kind::LEQ, {zero, rleaftasks[leaf]});
    Term constraint3 = s->mkTerm(cvc5::Kind::EQUAL, {constraint1, constraint2, terms[b-1]});
    s->assertFormula(constraint3);
}

void ipasir_reals_contained(void * solver, int position, int leaf, int b1, int b2){
    Solver *s = (Solver*)solver;
    Term pos = s->mkInteger(position);
    Term constraint1 = s->mkTerm(cvc5::Kind::EQUAL, {rleafs[leaf], pos});
    Term constraint2 = s->mkTerm(cvc5::Kind::AND, {constraint1, terms[b1-1]});
    Term constraint3 = s->mkTerm(cvc5::Kind::IMPLIES, {constraint2, terms[b2-1]});
    s->assertFormula(constraint3);

}

// returns task at leaf if solver is SAT
int ipasir_real_val_leaf(void * solver, int leaf){
    Solver *s = (Solver*)solver;
    return s->getValue(rleaftasks[leaf]).getInt32Value();
}
//#ifdef __cplusplus
//} // closing extern "C"
//#endif
