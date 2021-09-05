#include "formula_data_stucture.h"
using namespace std;

void re_init()
{
	// re init literals_
	for (int i = 0; i < MAX_VARS; i++)
	{
		for (int j = 0; j <= 1; j++)
		{
			literals_[i][j].antecedent_clause = 0;
			literals_[i][j].is_assigned = 0;
			literals_[i][j].is_unit = 0;
			literals_[i][j].literal_count = 0;
			free(literals_[i][j].literal_in_clauses);
			literals_[i][j].literal_in_clauses = NULL;
			free(literals_[i][j].location_in_clause);
			literals_[i][j].location_in_clause = NULL;
		}
	}

	// re init clauses
	for (int i = 0; i < original_size; i++)
	{
		free(clauses[i].literals_);
		clauses[i].literals_ = NULL;
	}
	free(clauses);
	clauses = NULL;
	original_size = current_size = 0;

	// re init changes information
	memset(changes, 0, sizeof(changes));
	changes_index = 0;
	memset(n_changes, 0, sizeof(n_changes));

	// re init assign
	memset(assign, 0, sizeof(assign));
	for (int i = 0; i < MAX_VARS; i++)
	{
		assign[i].type = UNASSIGNED;
	}
	
	// re init 
	contradictory_unit_clauses = 0;
	conflicting_literal = 0;
	memset(gucl_stack, 0, sizeof(gucl_stack));
	n_gucl = 0;

	depth = 0;
	backtrack_level = 0;

	memset(impl_clauses, 0, sizeof(impl_clauses));
	ic_cnt = 0;

	n_units = n_backtracks = 0;

	n_vars = max_clause_len = 0;

	memset(resolvent, 0, sizeof(resolvent));
	res_size = 0;

	resolvents_added = 0; 
	n_resolvents_threshold = 0;
	
	changes_occured = 0;

	memset(p_ijd, 0, sizeof(p_ijd));
	memset(sudoku, 0, sizeof(sudoku));
}


/*
*	dk(F, u) : the number of yet-to-be-satisfied clauses of length k in F that contain u
*	w(F, u) : a weight function with u

	We find a variable x that maximizes $(w(F,x), w(F,-x))
	and then we choose the literal x if w(F,x) >= w(f,-x) and choose -x otherwise
*/

/*
	2-sides-Jeroslow-Wang
	w(F,u) = sum of( 2^(-k) * dk(F,u) )
	$(s,t) = s+t

	since the 2^(-k) is difficult to calc,
	we calc 2^(max_clause_len - k) as a substitute for 2^(-k)
*/
int GetLiteral_2SJW()
{
	register int i, j, C;
	register unsigned int max = 0, r, s, t, mlen = max_clause_len;
	register int u = 0;
	for (i = 1; i <= n_vars; i++)
	{
		if (assign[i].decision == ASSIGN_NONE)
		{
			s = t = 0;
			for (j = 0; j < literals_[i][SATISFIED].literal_count; j++)
			{
				C = literals_[i][SATISFIED].literal_in_clauses[j];
				/*	if C is satisfied, then the following code doesnt work
					if C is satisfied, the s is w(F,u)						*/
				s += ((!clauses[C].is_satisfied) << (mlen - clauses[C].current_length));
			}
			for (j = 0; j < literals_[i][SHRUNK].literal_count; j++)
			{
				C = literals_[i][SHRUNK].literal_in_clauses[j];
				t += ((!clauses[C].is_satisfied) << (mlen - clauses[C].current_length));
			}
			r = s + t;		// $(s,t) = s+t	
			if (r > max)
			{
				max = r;
				if (s >= t) u = i;
				else u = -i;
			}
		}
	}
	return u;
}


/*
*	assign v as true
*/
void SetVar(int v)
{
	register int p = abs(v);
	register int q = (v > 0) ? SATISFIED : SHRUNK;

	/*
	* 	if C includes v, then mark C as satisfied
	*	and save change information for v
	*/
	for (register int i = 0; i < literals_[p][q].literal_count; i++)
	{
		register int j = literals_[p][q].literal_in_clauses[i];
		if (clauses[j].is_satisfied) continue;
		clauses[j].is_satisfied = true;

		current_size--;		// update the formula size
		changes[changes_index++].clause_index = j;
		n_changes[depth][SATISFIED]++;				//the number of clauses SATISFIED at depth ++

	}

	/*
	*	then set -p
	*/
	q = !q;
	for (register int i = 0; i < literals_[p][q].literal_count; i++)
	{
		register int j = literals_[p][q].literal_in_clauses[i];	// the ith clauses which contain literal is j
		if (clauses[j].is_satisfied) continue;
		register int k = literals_[p][q].location_in_clause[i];	// the location of literal in j is k
		clauses[j].current_length--;		// delete literal from j, then the current length of j decrease
		clauses[j].binary_code -= (1 << k);

		/*	update the information of changes
			the kth literal in clause j was changed
		*/
		changes[changes_index].clause_index = j;
		changes[changes_index].literal_index = k;
		changes_index++;
		n_changes[depth][SHRUNK]++;		// zhe SHRUNK clause in level depth increase

		/*	if the clause become a unit_clause	*/
		if (clauses[j].current_length == 1)
		{
			register int loc = int(log2(clauses[j].binary_code));	// the location of the only literal in cluase
			register int w = clauses[j].literals_[loc];				// w is the only literal in unit_clause j
			register int s = abs(w);
			register int t = (w > 0) ? SATISFIED : SHRUNK;

			/*	the literel w is assigned TRUE because of clause j	*/
			literals_[s][t].antecedent_clause = j;

			/*	if the -w has been assigned false, the conflict appears	*/
			if (literals_[s][!t].is_unit == true)
			{
				contradictory_unit_clauses = true;
				conflicting_literal = w;
			}

			/*	-w has not been assigned false	*/
			else if (literals_[s][t].is_unit == false)
			{
				/*	the stack of unit_clause_literal	*/
				gucl_stack[n_gucl] = clauses[j].current_unit_clause_literal = w;
				literals_[s][t].is_unit = true;
				n_gucl++;	// the size of stack gucl_stack increase
			}
		}
	}

	/*	update depth and backtrack level	*/
	if (depth && backtrack_level == depth - 1)
	{
		backtrack_level++;
	}
	depth++;

	/*	set v and -v as assigned	*/
	literals_[p][SATISFIED].is_assigned = true;
	literals_[p][SHRUNK].is_assigned = true;
}

/*
*	UnSetVar : recovering F from F|v
*/
void UnSetVar(int v)
{
	register int i;
	register int p = abs(v), q = (v > 0) ? SATISFIED : SHRUNK;

	/*	update depth and backtrack level */
	depth--;
	if (depth && backtrack_level == depth)
	{
		backtrack_level--;
	}

	/*	recover the changes brought by -v	*/
	while (n_changes[depth][SHRUNK])
	{
		n_changes[depth][SHRUNK]--;
		changes_index--;
		register int j = changes[changes_index].clause_index;
		register int k = changes[changes_index].literal_index;

		/*	increament length of c by 1*/
		clauses[j].current_length++;

		/*	if the clause was a unit_clause	*/
		if (clauses[j].current_length == 2)
		{

			/*	if the literal was set as unit then undo it	*/
			int s = abs(clauses[j].current_unit_clause_literal);
			int t = (clauses[j].current_unit_clause_literal > 0) ? SATISFIED : SHRUNK;
			literals_[s][t].is_unit = false;
			clauses[j].current_unit_clause_literal = 0;
		}

		/*	update binary code of c by 1	*/
		clauses[j].binary_code += (1 << k);
	}

	/*	recover the changes brought by v	*/
	while (n_changes[depth][SATISFIED])
	{
		n_changes[depth][SATISFIED]--;
		changes_index--;

		/*	mark c as note satisfied	*/
		register int j = changes[changes_index].clause_index;
		clauses[j].is_satisfied = false;

		/*	increament the formula size by 1	*/
		current_size++;
	}

	/*	set v and -v as unassigned	*/
	literals_[p][SATISFIED].is_assigned = false;
	literals_[p][SHRUNK].is_assigned = false;
}

int dpll()
{
	/********  Unit_propagation block  ************/
	int* lucl_stack = NULL;	// local unit_clause literal stack;
	register unsigned int  n_lucl = 0;	// the size of local unit_clause literal stack

	int* ml_stack = NULL;
	int n_ml = 0;

	while (true)
	{
		if (contradictory_unit_clauses)
		{
			ic_cnt = 0;
			int cl = abs(conflicting_literal);
			impl_clauses[ic_cnt++] = literals_[cl][SATISFIED].antecedent_clause;
			impl_clauses[ic_cnt++] = literals_[cl][SHRUNK].antecedent_clause;
			assign[cl].decision = assign[cl].decision = ASSIGN_NONE;
			while (n_lucl)
			{
				UnSetVar(lucl_stack[--n_lucl]);
				register int s = abs(lucl_stack[n_lucl]);
				register int t = lucl_stack[n_lucl] > 0 ? true : false;
				impl_clauses[ic_cnt++] = literals_[s][t].antecedent_clause;
				assign[s].type = UNASSIGNED;
				assign[s].decision = ASSIGN_NONE;
			}
			contradictory_unit_clauses = false;
			free(lucl_stack);
			n_gucl = 0;
			return UNSAT;
		}
		else if (n_gucl)
		{
			lucl_stack = (int*)realloc(lucl_stack, (n_lucl + 1) * sizeof(int));
			register int implied_lit = gucl_stack[--n_gucl];
			lucl_stack[n_lucl++] = implied_lit;
			assign[abs(implied_lit)].type = implied_lit > 0 ? true : false;
			assign[abs(implied_lit)].decision = ASSIGN_IMPLIED;
			SetVar(implied_lit);
			n_units++;
		}
		else break;
	}

	/*******  branching  *********/
	if (!current_size) return SAT;


	/*******	Monotone literal fixing	   *******/

	for (int i = 1; i < n_vars; i++)
	{
		int x, y, u, C;
		x = y = 0;		// x : the count of literal i in residual formula
						// y : the count of literal -i in residual formula
		if (assign[i].decision == ASSIGN_NONE)	// if the i and -1 has not been assigned
		{
			u = 0;	// the monotone literal
			for (int j = 0; j < literals_[i][SATISFIED].literal_count; j++)	// calc the count of x in resudual formula
			{
				C = literals_[i][SATISFIED].literal_in_clauses[j];
				x += (1 - clauses[C].is_satisfied);	//	if C is satisfie, it means this x is not in formula,  += 0
			}
			for (int j = 0; j < literals_[i][SHRUNK].literal_count; j++)
			{
				C = literals_[i][SHRUNK].literal_in_clauses[j];
				y += (1 - clauses[C].is_satisfied);
			}

			if (x && !y) u = i;
			if (y && !x) u = -i;
			if (u)	// if monotone literal has been found
			{
				ml_stack = (int*)realloc(ml_stack, (n_ml + 1) * sizeof(int));
				ml_stack[n_ml++] = u;
				assign[abs(u)].type = u > 0 ? true : false;
				assign[abs(u)].depth = depth;
				assign[abs(u)].decision = ASSIGN_IMPLIED;
				SetVar(u);
			}
		}
	}
	/****	end of Monotone literal fixing****/

	register int v = GetLiteral_2SJW();
	assign[abs(v)].type = v > 0 ? true : false;
	assign[abs(v)].depth = depth;
	assign[abs(v)].decision = ASSIGN_BRANCHED;

	SetVar(v);
	if (dpll()) return SAT;
	UnSetVar(v);

	assign[abs(v)].decision = ASSIGN_NONE;

	register int max_depth = 0, i, j, k, m, left = false;
	if (ic_cnt)
	{
		while (ic_cnt)
		{
			i = impl_clauses[--ic_cnt];
			k = clauses[i].original_length;
			for (j = 0; j < k; j++)
			{
				m = abs(clauses[i].literals_[j]);
				if (assign[m].decision == ASSIGN_BRANCHED && assign[m].depth > max_depth)
					max_depth = assign[m].depth;
			}
		}
		left = true;
	}

	/********  backtracking and backjumping  *************/

	n_backtracks++;
	if (backtrack_level >= depth - 1)
	{
		assign[abs(v)].type = !assign[abs(v)].type; // ???
		assign[abs(v)].decision = ASSIGN_IMPLIED;

		SetVar(-v);
		if (dpll()) return SAT;
		UnSetVar(-v);

		assign[abs(v)].type = UNASSIGNED;
		assign[abs(v)].decision = ASSIGN_NONE;

		if (left && ic_cnt)
		{
			while (ic_cnt)
			{
				i = impl_clauses[--ic_cnt];
				k = clauses[i].original_length;
				for (j = 0; j < k; j++)
				{
					m = abs(clauses[i].literals_[j]);
					if (assign[m].decision == ASSIGN_BRANCHED && assign[m].depth > max_depth)
						max_depth = assign[m].depth;
				}
			}
			if (max_depth < backtrack_level)
				backtrack_level = max_depth;
		}
	}

	/***	delete all you assignment you do in the function ato prepare for backtrack	***/
	while (n_ml)
	{
		int u = ml_stack[--n_ml];
		UnSetVar(u);
		assign[abs(u)].type = UNASSIGNED;
		assign[abs(u)].decision = ASSIGN_NONE;
	}
	ic_cnt = 0;
	while (n_lucl)
	{
		int z = lucl_stack[--n_lucl];
		UnSetVar(z);
		assign[abs(z)].type = UNASSIGNED;
		assign[abs(z)].decision = ASSIGN_NONE;
	}
	free(lucl_stack);
	contradictory_unit_clauses = false;
	return UNSAT;
}




/*	adding resolvents  */

int compute_resolvent(int x, int a, int b, int& len, int limit)
{
	register int j, k;
	int* check = (int*)calloc(n_vars + 1, sizeof(int));
	int found = false;
	int res_size = 0;	// the size of resolvent
	int C[2] = { a, b };
	for (j = 0; j < 2; j++)
	{
		for (k = 0; k < clauses[C[j]].original_length; k++)
		{
			register int w = abs(clauses[C[j]].literals_[k]);
			if (w == x) continue;
			else if (check[w] == clauses[C[j]].literals_[k]) continue;	// if two clauses have the same literal
			/*
			*	if another variables other than x appears in one of the clauses and appears complemented
			*	in other clause, then we return FALSE
			*/
			else if (check[w] == -clauses[C[j]].literals_[k])
			{
				free(check); return false;
			}
			/*
			*	 the unit_propagation may assigned some literals_
			*/
			else if (assign[abs(clauses[C[j]].literals_[k])].decision != ASSIGN_NONE) continue;
			else if (check[w] == 0)
			{
				check[w] = clauses[C[j]].literals_[k];
				resolvent[res_size++] = clauses[C[j]].literals_[k];
				if (res_size > limit)
				{
					free(check); return false;
				}
			}
		}
	}
	len = res_size;
	free(check);
	return true;
}

int get_restricted_resolvent(int x, int limit)
{
	register int i, j, k, a, b, res_length;
	int found;
	changes_occured = false;
	for (i = 0; i < literals_[x][SATISFIED].literal_count; i++)	// traverse clauses which contain x
	{
		a = literals_[x][SATISFIED].literal_in_clauses[i];
		if (clauses[a].is_satisfied == false)
		{
			for (j = 0; j < literals_[x][SHRUNK].literal_count; j++)	// traverse clauses which contain -x
			{
				b = literals_[x][SHRUNK].literal_in_clauses[j];
				if (clauses[b].is_satisfied == false)
				{
					found = compute_resolvent(x, a, b, res_length, limit);
					if (found)
					{
						if (resolvents_added < n_resolvents_threshold)
						{
							resolvents_added += add_a_clause_to_formula(resolvent, res_length);
							changes_occured = true;
						}
						else return -1; // if the count of resolvent reachs threshold
					}
				}
			}
		}
	}
	return -1;
}

int subsumable(int j, int k)
{
	register int i;
	int* check = (int*)calloc((n_vars + 1), sizeof(int));
	for (i = 0; i < clauses[k].original_length; i++)
	{
		check[abs(clauses[k].literals_[i])] = clauses[k].literals_[i];
	}
	for (i = 0; i < clauses[j].original_length; i++)
	{
		if (clauses[j].literals_[i] != check[abs(clauses[j].literals_[i])])
		{
			free(check); return false;
		}
	}
	free(check);
	return true;
}

int preprocess_subsume()
{
	register int n_subsume = 0;
	register int i, j, k, c1, c2, type;
	changes_occured = false;
	for (i = 1; i < n_vars; i++)
	{
		if (assign[i].decision != ASSIGN_NONE) continue;
		for (type = 0; type <= 1; type++) // type0 = SHRUNK, type1 = SATISFIED 
		{
			for (j = 0; j < literals_[i][type].literal_count; j++)
				for (k = 0; k < literals_[i][type].literal_count; k++)
				{
					if (j == k) continue;
					c1 = literals_[i][type].literal_in_clauses[j];
					c2 = literals_[i][type].literal_in_clauses[k];
					if (clauses[c1].is_satisfied || clauses[c2].is_satisfied) continue;
					if (clauses[c1].original_length >= clauses[c1].original_length) continue; // ???
					if (subsumable(c1, c2))
					{
						clauses[c2].is_satisfied = true;
						current_size--;
						n_subsume++;
						changes_occured = true;
					}
				}
		}
	}
	return n_subsume;
}

int clauses_present(int C[], int n)
{
	register int i, j, k, p, q;
	p = abs(C[0]);
	q = C[0] > 0 ? SATISFIED : SHRUNK;
	for (j = 0; j < literals_[p][q].literal_count; j++)
	{
		if (clauses[literals_[p][q].literal_in_clauses[j]].original_length == n)
		{
			int match_count = 0;
			for (k = 0; k < n; k++)
			{
				if (clauses[literals_[p][q].literal_in_clauses[j]].literals_[k] == C[k])
					match_count++;
				else break;
			}
			if (match_count == n) return true;
		}
	}
	return false;
}

int add_a_clause_to_formula(int C[], int n)
{
	register int i;
	qsort(C, n, sizeof(int), compare);
	if (clauses_present(C, n)) return false;
	clauses = (clause_info*)realloc(clauses, (original_size + 1) * sizeof(clause_info));
	clauses[original_size].is_satisfied = false;
	clauses[original_size].current_length = n;
	clauses[original_size].original_length = n;
	clauses[original_size].binary_code = (((1 << (n - 1)) - 1) << 1) + 1;	// is suitable for n == 32, 
	clauses[original_size].current_unit_clause_literal = 0;
	clauses[original_size].literals_ = (int*)malloc((n + 1) * sizeof(int));
	if (n > max_clause_len) max_clause_len = n;
	for (i = 0; i < n; i++)
	{
		int p = abs(C[i]);
		int q = C[i] > 0 ? SATISFIED : SHRUNK;


		literals_[p][q].literal_in_clauses =
			(int*)realloc(literals_[p][q].literal_in_clauses, (literals_[p][q].literal_count + 1) * sizeof(int));
		literals_[p][q].location_in_clause =
			(int*)realloc(literals_[p][q].location_in_clause, (literals_[p][q].literal_count + 1) * sizeof(int));
		literals_[p][q].literal_in_clauses[literals_[p][q].literal_count] = original_size;
		literals_[p][q].location_in_clause[literals_[p][q].literal_count] = i;
		literals_[p][q].literal_count++;
		literals_[p][q].is_assigned = false;
		clauses[original_size].literals_[i] = C[i];
		assign[p].decision = ASSIGN_NONE;
		assign[p].type = UNASSIGNED;
	}
	if (n == 1)
	{
		int s = abs(clauses[original_size].literals_[0]);
		int t = clauses[original_size].literals_[0] > 0 ? SATISFIED : SHRUNK;
		literals_[s][t].antecedent_clause = original_size;
		if (literals_[s][!t].is_unit == true)
		{
			contradictory_unit_clauses = true;
			conflicting_literal = clauses[original_size].literals_[0];
		}
		else if (literals_[s][t].is_unit == false)
		{
			gucl_stack[n_gucl] = clauses[original_size].literals_[0];
			clauses[original_size].current_unit_clause_literal = clauses[original_size].literals_[0];
			literals_[s][t].is_unit = true;
			n_gucl++;
		}
	}
	current_size++;
	original_size++;
	return true;
}

int preprocess()
{
	register int total_changes_occured, n_s = 0;
	if (original_size < 500) n_resolvents_threshold = original_size * 5;
	else if (original_size < 1000) n_resolvents_threshold = original_size * 4;
	else if (original_size < 1500) n_resolvents_threshold = original_size * 3;
	else if (original_size < 3000) n_resolvents_threshold = original_size * 2;
	else n_resolvents_threshold = original_size;
	/*
	while (1)
	{
		total_changes_occured = 0;
		/*
		if (preprocess_unit_propagarion() == UNSAT)
		{
			printf("Resolvents: °/0d\n", resolvent_added);
			printf("Subsumed: %d\n", n_s);
			return UNSAT;
		}

		//total_changes_occured += changes_occured;
		//preprocess_monotone_literal_fixing();
		//total_changes_occured += changes_occured;
		if (resolvents_added < n_resolvents_threshold)
		{
			for (int i = 1; i < n_vars; i++)
			{
				if(assign[i].decision == ASSIGN_NONE)
					if (get_restricted_resolvent(i, 3) == UNSAT)
					{
						printf("Resolvents: %d\n", resolvent_added);
						printf("Subsumed: °/„d\n", n_s);
						return UNSAT;
					}
				total_changes_occured += changes_occured;

			}
		}
		if (total_changes_occured == 0) break;
	}*/
	return -1;
}

void preprocess_monotone_literal_fixing()
{

}


void read()
{
	char c;		// store the first chatacter
	string s;	// dummy string
	int n_clauses = 0;

	while (true)
	{
		cin >> c;
		if (c == 'c') // if comment
		{
			getline(cin, s); // ignore
		}
		else
		{
			cin >> s;
			break;
		}
	}
	cin >> n_vars;
	cin >> n_clauses;
	int C[100];
	for (register int i = 0; i < n_clauses; i++)
	{
		memset(C, 0, sizeof(C));
		int j = 0;
		while (1)
		{
			cin >> C[j];
			if (C[j] == 0) break;
			j++;
		}
		add_a_clause_to_formula(C, j);
	}
}

void show_DPLL_result(int result, double duration_time)
{
	cout << "s" << endl;
	if (result == SAT)	cout << "SAT";
	else cout << "UNSAT";

	cout << endl << "v";
	if (result == SAT)
		for (int i = 1; i <= n_vars; i++)
		{
			cout << " ";
			if (assign[i].type == 0) cout << -i;
			else cout << i;
		}
	cout << endl;

	cout << "t ";
	cout << duration_time << "ms";

}

void sudoku_to_cnf()
{
	std::ofstream out("sudoku.cnf");
	if (!out)
	{
		cout << "can not open the file!";
	}

	int C[10]; // clause
	int literal_in_sudoku = 1; // the literal in suduku 
	int literal_count = 0; // the count of the literals in each clause

	for (int i = 1; i <= 9; i++)
		for (int j = 1; j <= 9; j++)
			for (int d = 1; d <= 9; d++)
			{
				p_ijd[i][j][d] = literal_in_sudoku++;

			}

	/*
	*	add initial digit to formula
	*/
	for (int i = 1; i <= 9; i++)
		for (int j = 1; j <= 9; j++)
		{
			if (sudoku[i][j])
			{
				int C[2];
				C[0] = p_ijd[i][j][sudoku[i][j]];
				add_a_clause_to_formula(C, 1);
			}
		}

	/*
	*	A clause ensure that the cell x[i][j] denotes one of the nine digits
		( 81 clauses in total )
	*/
	for (int i = 1; i <= 9; i++)
		for (int j = 1; j <= 9; j++)
		{
			literal_count = 0;
			for (int d = 1; d <= 9; d++)
			{
				C[literal_count++] = p_ijd[i][j][d];
			}
			add_a_clause_to_formula(C, literal_count);
		}

	/*
	*	36 clause to make sure the cell does not denote twe different digits at the same time
	*	81*36 clauses in total
	*/
	for (int i = 1; i <= 9; i++)
		for (int j = 1; j <= 9; j++)
		{
			literal_count = 0;
			for (int d1 = 1; d1 <= 9; d1++)
				for (int d2 = 1; d2 < d1; d2++)
				{
					C[literal_count++] = -p_ijd[i][j][d1];
					C[literal_count++] = -p_ijd[i][j][d2];
					add_a_clause_to_formula(C, 2);
				}

		}

	/*
	*	row
	*/
	for (int row = 1; row <= 9; row++) // for each row
	{
		for (int j = 1; j <= 9; j++)
			for (int k = 1; k < j; k++)
			{
				for (int digit = 1; digit <= 9; digit++)
				{
					literal_count = 0;
					C[literal_count++] = -p_ijd[row][j][digit];
					C[literal_count++] = -p_ijd[row][k][digit];
					add_a_clause_to_formula(C, literal_count);
				}
			}
	}

	/*
	*	column
	*/
	for (int column = 1; column <= 9; column++)
	{
		for (int i = 1; i <= 9; i++)
			for (int k = 1; k <= 9; k++)
			{
				for (int digit = 1; digit <= 9; digit++)
				{
					literal_count = 0;
					C[literal_count++] = -p_ijd[i][column][digit];
					C[literal_count++] = -p_ijd[k][column][digit];
					add_a_clause_to_formula(C, literal_count);
				}
			}
	}

	/*
	*	region
	*/
	for (int region = 1; region <= 9; region)
	{
		int init_row = (region / 3) * 3 + 1;
		int init_column = ((region - 1) % 3) * 3 + 1;
		for (int row1 = init_row; row1 <= init_row + 2; row1++)
			for (int column1 = init_column; column1 <= init_column + 2; column1++)
				for (int row2 = init_row; row2 <= row1; row2++)
					for (int column2 = init_column; column2 <= init_column + 2; column2++)
					{
						if (row2 = row1 && column2 >= column1) continue;
						for (int digit = 1; digit <= 9; digit++)
						{
							literal_count = 0;
							C[literal_count++] = -p_ijd[row1][column1][digit];
							C[literal_count++] = -p_ijd[row2][column2][digit];
							add_a_clause_to_formula(C, 2);
						}
					}
	}


}

void show_sudoku()
{
	int literal_num = 0;
	for (int i = 1; i <= 9; i++)
	{
		for (int j = 1; j <= 9; j++)
		{

			for (int digit = 1; digit <= 9; digit++)
			{
				literal_num++;
				if (assign[literal_num].type == true && sudoku[i][j] == 0)
					sudoku[i][j] = digit;
			}
			cout << sudoku[i][j] << " ";
		}
		cout << endl;
	}
}

void create_sudoku()
{
	
}

int main()
{
	clock_t start, finish;
	double duration;
	char filename[100];
	init();

	while (1)
	{
		system("cls");
		cout << "1.解决SAT问题" << endl;
		cout << "2.解决数独" << endl;
		cout << "0.退出系统" << endl;
		int operation;
		cin >> operation;
		switch (operation)
		{
		case 0:
			break;
		case 1:
			cout << "请输入文件名:";
			cin >> filename;
			read();
			start = clock();
			int result = dpll();
			finish = clock();
			duration = (double)(finish - start);
			show_DPLL_result(result, duration);
			break;
		case 2:
			create_sudoku();
			sudoku_to_cnf();
			show_sudoku();
			cout << "数独的cnf文件已输入到sudoku.cnf" << endl;
			cout << "按任意键解决该数独..." << endl;
			getchar();
			dpll();
			show_sudoku();
			break;
		default:
			break;
		}
		re_init();
		if (operation == 0) break;
	}
	return 0;
}


