#pragma once


#ifndef formula_data_structure
#define formula_data_structure

#include <iostream>
#include <cmath>
#include <string>
#include <cstring>
#include <stdlib.h>
#include <fstream>
#include <time.h>

#define UNSAT 0
#define SAT 1

#define MAX_VARS 1000
#define MAX_CLAUSES 10000

#define SATISFIED 1
#define	SHRUNK 0

#define UNASSIGNED -1

#define ASSIGN_NONE 0
#define ASSIGN_BRANCHED 1
#define ASSIGN_IMPLIED 2
#define ASSIGN_REMOVED 3

/*
	information of the literal
*/
typedef struct literal_info
{
	int is_assigned;			// store the assignment information
	int literal_count;			// the count of the literal
	int* literal_in_clauses;	// list of clauses in the original formula that contain the literal
	int* location_in_clause;	// the list of locations of the literal in the corresponding clauses
	int is_unit;				// if literal becomes the only unassigned literal in a clause C, the is_unit field is set to YES;
	int antecedent_clause;		// if is_unit field of a literal is set to YES because of C, then C is recorded in the antecedent_clause field;

} literal_info;

/*
	literals[j][SARISFIED] store the information related to literal
	literals[j][SHRUNK] store the information related to -j
*/
literal_info** literals_;

/*
	information of the clauses
*/
typedef struct clause_info
{
	int* literals_;
	int current_length;		// when a literal in the clause is set to FALSE, the current_length decreases by one
	int original_length;
	int is_satisfied;

	/*
		binary_code holds an integer, the binary of which corresponds to the bitstring
		obtained from the literals setting '1' if UNASSIGNED and '0' if FALSE
	*/
	int binary_code;

	/*
		store the unit-clause-literal if the clause has become unit
		store zero otherwise
	*/
	int current_unit_clause_literal;
} clause_info;

clause_info* clauses;

/*
	original_size : original number of clausess of the formula
	current_size  : current number of clauses of the formula
*/
int original_size, current_size;

/*
	structure to keep track of changes made while computing the residual
	formula and is used when the changes are needed to be reversed
*/
typedef struct changes_info
{
	/*
		When the is_satisf ied field of a clause is changed to YES, the clause-index
		is saved. When a currently unassigned literal in a clause is set to FALSE, both the
		clause-index and the literal-index are saved in clause_index and literal_index
		respectively */
	int clause_index;
	int literal_index;
} changes_info;

changes_info changes[MAX_CLAUSES];		// store all the changes
unsigned int changes_index;				// the index of changes
/*
	n_changes[depth][SATISFIED] : the number of clauses satisfied(or resolved) at shrunk at level depth
	n_changes[depth][SHRUNK]    : the number of clauses shrunk
	*/
unsigned int n_changes[MAX_VARS][2];

typedef struct assign_info
{
	int type;		// the value of the assigned literal, TRUE or FALSE or UNASSIGNED
	int depth;		// the depth at which the assignment is made
	/*
		ASSIGN_BRANCHED : the literal was chosen by a branching decision
		ASSIGN_IMPLIED  : the literal was forced to have an assignment
		ASSIGN_NONE		: the literal has not been assigned
		ASSIGN_REMOVED  : the literal was removed from the fomula
		by default the field decision stores ASSIGN_NONE
	*/
	int decision;
} assign_info;

// the stucture is used to compute backtracking levels for none-chronological backtracking
assign_info assign[MAX_VARS];


/*
	YES: when x and -x are the only unassigned literal in two clauses
	if the variable is set to YES, then we return UNSAT*/
bool contradictory_unit_clauses;

int conflicting_literal;	//one of the conflicting literal 

/*
	when a new unit clause is detected,
	the unit-clause-literal is stored in global array gucl_stack*/
int gucl_stack[MAX_VARS];
int n_gucl;					//the size of gucl_stack

/*
	depth      : the level of a node in the branching tree

	*/
int depth, backtrack_level; //max_depth;

int impl_clauses[MAX_VARS];	//  store the antecedent clauses in an unit-propagation that leads to a contradiction.
int ic_cnt;			// the size of the impl_clauses(store the antecedent clauses in an unit-propagation that leads to a contradiction);

int n_units;
int n_backtracks;

int n_vars;
int max_clause_len;

int resolvent[40];	// scanning through the clauses to obtain a resolvent
int res_size;	// the index of resolvent

int resolvents_added;		// the number of resolvents added so far
int n_resolvents_threshold;	// the number of resolvents we are allowed to add

int changes_occured;

int compare(const void* a, const void* b)
{
	return *(int*)a - *(int*)b;
}
int add_a_clause_to_formula(int C[], int n);



void init()
{
	// init literals_

	literals_ = (literal_info**)malloc(MAX_VARS * sizeof(literal_info*));
	for (int i = 0; i < MAX_VARS; i++)
	{
		literals_[i] = (literal_info*)malloc(2 * sizeof(literal_info));

		literals_[i][0].literal_in_clauses = NULL;
		literals_[i][0].location_in_clause = NULL;

		literals_[i][1].literal_in_clauses = NULL;
		literals_[i][1].location_in_clause = NULL;

		literals_[i][1].literal_count = 0;
		literals_[i][0].literal_count = 0;

		literals_[i][0].is_assigned = 0;
		literals_[i][1].is_assigned = 0;
		literals_[i][0].antecedent_clause = 0;
		literals_[i][1].antecedent_clause = 0;
		literals_[i][0].is_unit = 0;
		literals_[i][1].is_unit = 0;
	}

	for (int i = 0; i < MAX_VARS; i++)
	{
		assign[i].type = UNASSIGNED;
	}
	
}




/*suduku*/

int p_ijd[10][10][10]; // the truth value of the equation (xij = d)
int sudoku[10][10];

#endif // !formula_data_structure