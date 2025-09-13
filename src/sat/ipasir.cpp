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





#include "ipasir.h"

Sort boolSort;
std::vector<Term> terms;
int tsize = 128;
bool firstloop = true;
std::vector<Term> ors;

#if !defined SAT_ENCODING || defined ONLY_ORDERING
Sort intSort;
std::vector<Term> rleafpos;
std::vector<Term> constants;
int numIVars;
int numIFormulas;
#endif

#ifndef SAT_ENCODING
std::vector<Term> rleaftasks;
std::vector<Term> rpostasks;

#ifdef USE_TUPLES
Sort tupleSort;
Sort setSort;
std::vector<Term> rleafs;
Term posset;
#endif
#endif

/**
 * Return the name and the version of the incremental SAT
 * solving library.
 */
IPASIR_API const char * ipasir_signature (){
#ifdef SAT_ENCODING
    return "cvc SAT encoding" ORDERNAME SUCCESSORNAME;
#else
    return "cvc SMT encoding" DISTINCTNAME SUCCESSORNAME TUPLENAME;
#endif
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
    Solver *solver = new Solver();
    solver->setOption("produce-models", "true");
    //solver->setOption("produce-unsat-cores", "true");
    boolSort = solver->getBooleanSort();
#if !defined SAT_ENCODING || defined ONLY_ORDERING
    intSort = solver->getIntegerSort();
#ifdef USE_TUPLES
    tupleSort = solver->mkTupleSort({intSort, intSort});
    setSort = solver->mkSetSort(tupleSort);
#endif
    numIVars = 0;
    numIFormulas = 0;
#endif

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
    Solver *s = (Solver*)solver;
    delete s;
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
    Solver *s = (Solver*)solver;
    Result r1 = s->checkSat();
    if(r1.isSat()){
#if !defined SAT_ENCODING || defined ONLY_ORDERING
        std::cout << "Formula additionally has " << numIVars << " integer variables and " << numIFormulas << " integer formulas." << std::endl;
#endif
        /*return 10;
        for(const Term& t :rleafpos){
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
        }*/
        return 10;
    }
    if (r1.isUnsat()){
        return 20;
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

#if !defined SAT_ENCODING || defined ONLY_ORDERING
void ipasir_init_reals(void * solver, int numVertices, int numPositions, int numTasks){
    // initiate integer terms for tracking position/task each leaf is at
    // initiate integer term for tracking task done at each position
    // initiate constant integer terms
    // 2 l + p terms, max(p, t) constants
    Solver *s = (Solver*)solver;

    constants.resize(std::max(numPositions, numTasks));
    for(int c = 0; c < std::max(numPositions, numTasks); c++){
        Term ct = s->mkInteger(c);
        constants[c] = ct;
    }

    rleafpos.resize(numVertices);
#ifndef ONLY_ORDERING
    rleaftasks.resize(numVertices);
#ifdef USE_TUPLES
    rleafs.resize(numVertices);
#endif
#endif
 	for (int l = 0; l < numVertices; l++){
        Term lp = s->mkConst(intSort, "leaf" + std::to_string(l) + "pos");
        rleafpos[l] = lp;
        numIVars += 1;
#ifndef ONLY_ORDERING
        Term lt = s->mkConst(intSort, "leaf" + std::to_string(l) + "task");
        rleaftasks[l] = lt;
        numIVars += 1;
#ifdef USE_TUPLES
        Term ls = s->mkTuple({lp, lt});
        rleafs[l] = ls;
        numIVars += 1;
#endif
#endif
    }

#ifndef ONLY_ORDERING
#ifndef NDISTINCT
    Term distinct = s->mkTerm(cvc5::Kind::DISTINCT, rleafpos);
    s->assertFormula(distinct);
    numIFormulas += 1;
#else
    for (int i = 0; i < numVertices; i++){
        for (int j = 0; j < i; j++){
            Term distinct = s->mkTerm(cvc5::Kind::DISTINCT, {rleafpos[i], rleafpos[j]});
            s->assertFormula(distinct);
            numIFormulas += 1;
        }
    }
#endif


    rpostasks.resize(numPositions);
#ifdef USE_TUPLES
    std::vector<Term> tset;
    posset = s->mkEmptySet(setSort);
#endif

    for(int p = 0; p < numPositions; p++){
        Term pt = s->mkConst(intSort, "pos" + std::to_string(p) + "task");
#ifdef USE_TUPLES
        Term tup = s->mkTuple({constants[p], pt});
        tset.push_back(tup);
        numIVars += 1;
#endif
        rpostasks[p] = pt;
        numIVars += 1;
    }

#ifdef USE_TUPLES
    tset.push_back(posset);
    posset = s->mkTerm(cvc5::Kind::SET_INSERT, tset);
    numIVars += 1;
#endif
#endif //ONLY_ORDERING
}

void ipasir_leafs_successor(void * solver, int l, int succ){
    // if a leaf has an active successor, then it must be at an earlier position than the successor
    // at most l x l constraints
    Solver *s = (Solver*)solver;
    //Term constraint1 = s->mkTerm(cvc5::Kind::LEQ, {constants[0], rleafpos[succ]});
    Term constraint2 = s->mkTerm(cvc5::Kind::LT, {rleafpos[l], rleafpos[succ]});
    //Term constraint3 = s->mkTerm(cvc5::Kind::IMPLIES, {constraint1, constraint2});
    s->assertFormula(constraint2);
    numIFormulas += 1;
}

#endif

#ifndef SAT_ENCODING

void ipasir_constrain_leaf_positions(void * solver, int l, int firstPossible, int lastPossible){
    // constrain each leaf to only be in positions it is allowed to be
    // at most 2*l constraints
    Solver *s = (Solver*)solver;

    //std::cout << "fp" << firstPossible << " lp" << lastPossible << "\n";
    //if(firstPossible > 0){
    Term first = s->mkTerm(cvc5::Kind::LEQ, {constants[firstPossible], rleafpos[l]});
    //    Term inactive = s->mkTerm(cvc5::Kind::LT, {rleafpos[l], constants[0]});
    //    Term c = s->mkTerm(cvc5::Kind::OR, {first, inactive});
    s->assertFormula(first);
    numIFormulas += 1;
    //}
    Term last = s->mkTerm(cvc5::Kind::LEQ, {rleafpos[l], constants[lastPossible]});
    s->assertFormula(last);
    numIFormulas += 1;
}

void ipasir_constrain_leaf_tasks(void * solver, int l, PDT * leaf){
    // constrain each leaf to only do tasks it can perform
    // also turn on the appropriate boolean primitive for leaf/task pairs
    // l terms, at most l*t + l constraints
    Solver *s = (Solver*)solver;

    if (leaf->possiblePrimitives.size() == 0) {
        Term constraint = (s->mkTerm(cvc5::Kind::LT, {rleaftasks[l], constants[0]}));
        s->assertFormula(constraint);
        numIFormulas += 1;
        return;
    }

    std::vector<Term> constraints;
    for (int prim = 0; prim < leaf->possiblePrimitives.size(); prim++){
        if (leaf->primitiveVariable[prim] == -1) continue; // pruned
        Term leaftask = s->mkTerm(cvc5::Kind::EQUAL, {rleaftasks[l], constants[leaf->possiblePrimitives[prim]]});
        int b = leaf->primitiveVariable[prim];
        Term c = s->mkTerm(cvc5::Kind::EQUAL, {leaftask, terms[b-1]});
        s->assertFormula(c);
        numIFormulas += 1;
        constraints.push_back(leaftask);
    }
    constraints.push_back(s->mkTerm(cvc5::Kind::LT, {rleaftasks[l], constants[0]}));
    Term constraint = s->mkTerm(cvc5::Kind::OR, constraints);
    s->assertFormula(constraint);
    numIFormulas += 1;
}

void ipasir_constrain_position_tasks(void * solver, int p, int numVertices){
    // constrain each position to perform the task performed by the leaf at that position
    // constrain each position without leaf to not perform a task
    // p terms, l x p + p constraints
    Solver *s = (Solver*)solver;

#ifndef USE_TUPLES
    std::vector<Term> constraints;
    for(int l = 0; l < numVertices; l++){
        Term c1 = s->mkTerm(cvc5::Kind::EQUAL, {rleafpos[l], constants[p]});
        Term c2 = s->mkTerm(cvc5::Kind::EQUAL, {rleaftasks[l], rpostasks[p]});
        Term c3 = s->mkTerm(cvc5::Kind::IMPLIES, {c1, c2});
        s->assertFormula(c3);
        numIFormulas += 1;
        constraints.push_back(c1);
    }
    constraints.push_back(s->mkTerm(cvc5::Kind::LT, {rpostasks[p], constants[0]}));
    Term constraint = s->mkTerm(cvc5::Kind::OR, constraints);
#else
    Term constraint = s->mkTerm(cvc5::Kind::SET_MEMBER, {rleafs[p], posset});
#endif
    s->assertFormula(constraint);
    numIFormulas += 1;
}

void ipasir_primitive_position_tasks(void * solver, int p, int t, int b){
    // if task t is done at position p turn on the primitive boolean
    // t x p constraints
    Solver *s = (Solver*)solver;
    Term c1 = s->mkTerm(cvc5::Kind::EQUAL, {rpostasks[p], constants[t]});
    Term c2 = s->mkTerm(cvc5::Kind::EQUAL, {c1, terms[b-1]});
    s->assertFormula(c2);
    numIFormulas += 1;
}

// returns task at leaf if solver is SAT
int ipasir_real_val_leaf(void * solver, int leaf){
    Solver *s = (Solver*)solver;
    return s->getValue(rleaftasks[leaf]).getInt32Value();
}

// returns leaf at position if solver is SAT
int ipasir_real_leaf_pos(void * solver, int pos){
    Solver *s = (Solver*)solver;
    for (int l = 0; l < rleafpos.size(); l++){
        if (s->getValue(rleafpos[l]).getInt32Value() == pos){
            return l;
        }
    }
    return -1;
}

// returns task at position if solver is SAT
int ipasir_real_val_pos(void * solver, int pos){
    Solver *s = (Solver*)solver;
    return s->getValue(rpostasks[pos]).getInt32Value();
}
#endif

#ifdef ONLY_ORDERING
void ipasir_primitive_constrain_leaf(void * solver, int l, int p, int b){
    // constrain leaf by primitive

    Solver *s = (Solver*)solver;

    Term c1 = s->mkTerm(cvc5::Kind::EQUAL, {rleafpos[l], constants[p]});
    Term c2 = s->mkTerm(cvc5::Kind::EQUAL, {c1, terms[b-1]});
    s->assertFormula(c2);
    numIFormulas += 1;
}
#endif
