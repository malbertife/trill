/*
	LPAD and CP-Logic reasoning suite
	File semlpadsld.pl
	Program for building the semantics of an LPAD
	Queries are answered by using Prolog in every instance
	Copyright (c) 2007, Fabrizio Riguzzi
*/

:-module(semlphkb,[p/1,s/2,s/3,sc/3,set/2]).
:-use_module(library(lists)).
:-use_module(library(apply)).
:-dynamic setting/2.
:-set_prolog_flag(unknown,fail).


setting(epsilon,0.00001).
setting(ground_body,false).
/* available values: true, false
if true, both the head and the body of each clause will be grounded, otherwise
only the head is grounded. In the case in which the body contains variables
not appearing in the head, the body represents an existential event */

setting(grounding,variables).
/* available values: variables, modes
if set to variables, the universe facts from the .uni file are used
if set to modes, the mode and type declaration from the .uni file are used
*/

setting(verbose,false).


sc(Goals,Evidence,Prob):-
	s(Evidence,ProbE),
	append(Goals,Evidence,GE),
	s(GE,ProbGE),
	Prob is ProbGE/ProbE.

s(GoalsList,Prob):-
	program_names(L),
	list2and(GoalsList,Goals),
	run_query(L,Goals,0,Prob).

run_query([],_G,P,P).

run_query([Prog|T],Goal,PIn,POut):-
	elab_conj(Prog,Goal,Goal1),
	call(Goal1),
	prob(Prog,P),
	P1 is PIn+P,
	run_query(T,Goal,P1,POut).

run_query([Prog|T],Goal,PIn,POut):-
	elab_conj(Prog,Goal,Goal1),
	\+ call(Goal1),
	run_query(T,Goal,PIn,POut).

s(Goal,File,Prob) :-
	retractall(probt(_)),
	assert(probt(0)),
	clean_db,
	atom_concat(File,'.cpl',FilePl),
	open(FilePl,read,S),
	read_clauses(S,C),
	close(S),
	%atom_concat(File,'.uni',FileUni),
	%consult(FileUni),
	process_clauses(C,ClausesVar),
	instantiate(ClausesVar,[],Clauses),!,
	s1(Goal,Clauses,Prob).

s1(Goal,Clauses,_Prob):-
	assert(program(1)),
	assert(program_names([])),
	create_programs(Clauses,Program),
	(solve(Goal) ->
		(rule(prob(P):-true),
		 clean_db_end(Program),
		 probt(PIn),
		 P1 is PIn+P,
		 retractall(probt(_)),
		 assert(probt(P1))
		)
	 ;
		clean_db_end(Program)
	),
	fail.

s1(_,_,Prob):-
	probt(Prob).

/* predicate for parsing the program file */
p(File):-
	clean_db,
	atom_concat(File,'.cpl',FilePl),
	open(FilePl,read,S),
	read_clauses(S,C),
	close(S),
	%atom_concat(File,'.uni',FileUni),
	%consult(FileUni),
	process_clauses(C,ClausesVar),
	instantiate(ClausesVar,[],Clauses),
	assert(program(1)),
	assert(program_names([])),
	create_programs(Clauses).

clean_db:-
	%findall((P/A),(mode(Atom),functor(Atom,P,A0),A is A0+1),L),
	%abolish_all(L),
	abolish(program/1),
	abolish(program_names/1),
	abolish(prob/2).

clean_db_end([]):- !,
	retractall(rule(_H:-_B)).

clean_db_end([(_H:-_B)|T]):- !,
	clean_db_end(T).

clean_db_end([H|T]):- !,
	remove_axiom(H),
	clean_db_end(T).

abolish_all([]).

abolish_all([(P/A)|T]):-
	abolish(P/A),
	abolish_all(T).

/* create_programs(Clauses)
	create the instances of the ground LPAD composed by Clauses
	Each instance is identified by an atom of the form P<Number> where <Number> is an
	increasing number. An extra argument is added to each atom in the clauses to represent
	the identifier of the instance.
*/
create_programs(Clauses,Program):-
	create_single_program(Clauses,1,Program),
	retract(program(N)),
	number_codes(N,NC),
	atom_codes(NA,NC),
	atom_concat(p,NA,Name),
	N1 is N+1,
	assert(program(N1)),
	(setting(verbose,true)->
		format("Writing instance ~d~n",[N])
	;
		true
	),
	write_program(Name,Program),
	retract(program_names(L)),
	append(L,[Name],L1),
	assert(program_names(L1)).

create_programs(_).


write_program(_Name,[]).

write_program(Name,[(H:-B)|T]):-
	%elab_conj(Name,H,H1),
	%elab_conj(Name,B,B1),
	assertz(rule(H:-B)),
	write_program(Name,T).

write_program(Name,[H|T]):-
	H\=(_:-_),
	(H=('':_) -> true ; add_axiom(H)),
	write_program(Name,T).

/* elab_conj(Name,Conj0,Conj)
	adds the extra argument Name to the conjunction Conj0 resulting in Conj
*/
elab_conj(_Name,true,true):-!.

elab_conj(Name,\+(B),\+(B1)):-!,
	elab_conj(Name,B,B1).

elab_conj(Name,(BL,Rest),(BL1,Rest1)):-!,
	elab_conj(Name,BL,BL1),
	elab_conj(Name,Rest,Rest1).

elab_conj(Name,bagof(V,EV^G,L),bagof(V,EV^GL,L)):-!,
	elab_conj(Name,G,GL).

elab_conj(Name,bagof(V,G,L),bagof(V,GL,L)):-!,
	elab_conj(Name,G,GL).

elab_conj(Name,setof(V,EV^G,L),setof(V,EV^GL,L)):-!,
	elab_conj(Name,G,GL).

elab_conj(Name,setof(V,G,L),setof(V,GL,L)):-!,
	elab_conj(Name,G,GL).

elab_conj(Name,findall(V,G,L),findall(V,GL,L)):-!,
	elab_conj(Name,G,GL).

elab_conj(_Name,A,A):-
	bg(A),!.

elab_conj(_Name,A,A):-
	builtin(A),!.

elab_conj(Name,Lit,Lit1):-
	Lit\=(_,_),
	Lit=..[Pred|Args],
	Lit1=..[Pred,Name|Args].


create_single_program([],P,[(prob(P):-true)]).

create_single_program([r(H,B)|T],PIn,[(HA:-B)|T1]):-
	member((HA:P),H),
	P1 is PIn*P,
	create_single_program(T,P1,T1).

create_single_program([r(H)|T],PIn,Res):-
	member((HA:P),H),
	P1 is PIn*P,
	create_single_program(T,P1,T1),
	(HA = '' -> Res = T1 ; Res = [HA|T1]).


/* predicates for producing the ground instances of program clauses */

/* instantiate(Clauses,C0,C)
	returns in C the set of clauses obtained by grounding Clauses
*/
instantiate([],C,C).

instantiate([r(_V,[H:1],B)|T],CIn,COut):-!,
	append(CIn,[r([H:1],B)],C1),
	instantiate(T,C1,COut).

instantiate([r(V,H,B)|T],CIn,COut):-
	(setting(grounding,variables)->
		findall(r(H,BOut),instantiate_clause_variables(V,H,B,BOut),L)
	;
		findall(r(H,BOut),instantiate_clause_modes(H,B,BOut),L)
	),
	append(CIn,L,C1),
	instantiate(T,C1,COut).

instantiate([r(_V,H)|T],CIn,COut):-
	append(CIn,[r(H)],C1),
	instantiate(T,C1,COut).

instantiate_clause_modes(H,B,BOut):-
	instantiate_head_modes(H),
	list2and(BL,B),
	instantiate_body_modes(BL,BLOut),
	list2and(BLOut,BOut).


instantiate_head_modes([]):-!.

instantiate_head_modes([H:_P|T]):-
	instantiate_atom_modes(H),
	instantiate_head_modes(T).


instantiate_body_modes(BL,BL):-
	setting(ground_body,false),!.

instantiate_body_modes(BL0,BL):-
	instantiate_list_modes(BL0,BL).


instantiate_list_modes([],[]).

instantiate_list_modes([H|T0],T):-
	builtin(H),!,
	call(H),
	instantiate_list_modes(T0,T).

instantiate_list_modes([\+ H|T0],T):-
	builtin(H),!,
	\+ call(H),
	instantiate_list_modes(T0,T).

instantiate_list_modes([\+ H|T0],[\+ H|T]):-!,
	instantiate_atom_modes(H),
	instantiate_list_modes(T0,T).

instantiate_list_modes([H|T0],[H|T]):-
	instantiate_atom_modes(H),
	instantiate_list_modes(T0,T).


instantiate_atom_modes(''):-!.

instantiate_atom_modes(A):-
	functor(A,F,NArgs),
	functor(TA,F,NArgs),
	A=..[F|Args],
	mode(TA),
	TA=..[F|Types],
	instantiate_args_modes(Args,Types).


instantiate_args_modes([],[]):-!.

instantiate_args_modes([H|T],[TH|TT]):-
	type(TH,Constants),
	member(H,Constants),
	instantiate_args_modes(T,TT).


instantiate_clause_variables([],_H,B,BOut):-
	list2and(BL,B),
	(setting(ground_body,true)->
		check_body(BL,BLOut)
	;
		BLOut=BL
	),
	list2and(BLOut,BOut).

instantiate_clause_variables([VarName=Var|T],H,BIn,BOut):-
	universe(VarNames,U),
	member(VarName,VarNames),
	member(Var,U),
	instantiate_clause_variables(T,H,BIn,BOut).

instantiate_clause_variables([VarName=_Var|T],H,BIn,BOut):-
	\+ varName_present_variables(VarName),!,
	instantiate_clause_variables(T,H,BIn,BOut).


varName_present_variables(VarName):-
	universe(VarNames,_U), member(VarName,VarNames).

/* check_body(Body0,Body)
	removes the true builtin literals from Body0. Fails if there is a false builtin literal.
*/
check_body([],[]).

check_body([H|T],TOut):-
	builtin(H),!,
	call(H),
	check_body(T,TOut).

check_body([H|T],[H|TOut]):-
	check_body(T,TOut).


/* predicates for processing the clauses read from the file */
/* process_clauses(Terms,Clauses)
	processes Terms to produce Clauses
	Terms is a list contatining elements of the form
	((H:-B),V)
	Clauses is a list containing elements of the form
	r(V,HL,BL)
	where HL is the list of disjuncts in H and BL is the list
	of literals in B
*/

process_clauses(L,LResult):-
	remove_prob_annot_ax(L,ProbAnnotAx,LPruned),
	process_clauses(LPruned,ProbAnnotAx,LResult).

process_clauses([(end_of_file,[])],_,[]).

process_clauses([((H:-B),V)|T],ProbAnnotAx,[r(V,HL,B)|T1]):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,HLPList),
	manage_lp_axioms(T,HLPList,T0),
	process_clauses(T0,ProbAnnotAx,T1).

process_clauses([((H:-B),V)|T],ProbAnnotAx,[r(V,HL,B)|T1]):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,HLPList),
	manage_lp_axioms(T,HLPList,T0),
	process_clauses(T0,ProbAnnotAx,T1).

process_clauses([((H:-B),V)|T],ProbAnnotAx,[r(V,[H:1],B)|T1]):-!,
	functor(H,Pred,Arity),
	manage_lp_axioms(T,[Pred/Arity],T0),
	process_clauses(T0,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL,true)|T1]):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,HLPList),
	manage_lp_axioms(T,HLPList,T0),
	process_clauses(T0,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL,true)|T1]):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,HLPList),
	manage_lp_axioms(T,HLPList,T0),
	process_clauses(T0,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL)|T1]):-
	H=..[P|_Args],
	owl2_model:is_axiom(P),!,
	process_axiom(H,ProbAnnotAx,HL),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,[H:1],true)|T1]):-
	functor(H,Pred,Arity),
	manage_lp_axioms(T,[Pred/Arity],T0),
	process_clauses(T0,ProbAnnotAx,T1).

/* managess lpClassAssertion and lpPropertyAssertion following the clauses */
manage_lp_axioms(C,LPList,NC):-
	create_lp_axioms(LPList,NLPList),
	add_lp_axioms(C,NLPList,NC).

create_lp_axioms([],[(end_of_file,[])]).

create_lp_axioms([P/1|T],[(lpClassAssertion(P),[])|T1]):- !,
	create_lp_axioms(T,T1).

create_lp_axioms([P/2|T],[(lpPropertyAssertion(P),[])|T1]):- !,
	create_lp_axioms(T,T1).

create_lp_axioms([_P/_A|T],T1):-
	create_lp_axioms(T,T1).

add_lp_axioms(T,[],T).

add_lp_axioms(T,HLPList,T1):-
	delete(T,(end_of_file,[]),T0),
	append(T0,HLPList,T1).

remove_prob_annot_ax([],[],[]).

remove_prob_annot_ax([(annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(Prob)),[])|T],[(Ax,Prob)|T1],T2):- !,
	remove_prob_annot_ax(T,T1,T2).

remove_prob_annot_ax([H|T],T1,[H|T2]):-
	remove_prob_annot_ax(T,T1,T2).

process_head([H:PH],P,[H:PH1|Null],[Pred/Arity]):-
	PH1 is PH,
	PNull is 1-P-PH1,
	setting(epsilon,Eps),
	EpsNeg is - Eps,
	PNull > EpsNeg,
	(PNull>Eps->
		Null=['':PNull]
	;
		Null=[]
	),
	functor(H,Pred,Arity).

process_head([H:PH|T],P,[H:PH1|NT],[Pred/Arity|LPList]):-
	PH1 is PH,
	P1 is P+PH1,
	functor(H,Pred,Arity),
	process_head(T,P1,NT,LPList).

process_axiom(Ax,ProbAnnotAx,H):-
	(member((Ax,ProbAT),ProbAnnotAx) ->
		(atom_number(ProbAT,ProbA),
		 PH1 is ProbA,
		 PNull is 1-PH1,
		 H=[Ax:PH1,'':PNull]
		)
	 ;
		(H=[Ax:1])
	 ).

/* predicates for reading in the program clauses */
/* read_clauses(S,Clauses)
	read Clauses from stream S
*/
read_clauses(S,Clauses):-
	(setting(ground_body,true)->
		read_clauses_ground_body(S,Clauses)
	;
		read_clauses_exist_body(S,Clauses)
	).


read_clauses_ground_body(S,[(Cl,V)|Out]):-
	read_term(S,Cl,[variable_names(V)]),
	(Cl=end_of_file->
		Out=[]
	;
		read_clauses_ground_body(S,Out)
	).


read_clauses_exist_body(S,[(Cl,V)|Out]):-
	read_term(S,Cl,[variable_names(VN)]),
	extract_vars_cl(Cl,VN,V),
	(Cl=end_of_file->
		Out=[]
	;
		read_clauses_exist_body(S,Out)
	).


/* extract_vars_cl(Clause,VariableNames,Couples)
	extract from Clause couples of the form VariableName=Variable
*/
extract_vars_cl(end_of_file,[],[]).

extract_vars_cl(Cl,VN,Couples):-
	(Cl=(H:-_B)->
		true
	;
		H=Cl
	),
	extract_vars(H,[],V),
	pair(VN,V,Couples).


pair(_VN,[],[]).

pair([VN= _V|TVN],[V|TV],[VN=V|T]):-
	pair(TVN,TV,T).


extract_vars(Var,V0,V):-
	var(Var),!,
	(member_eq(Var,V0)->
		V=V0
	;
		append(V0,[Var],V)
	).

extract_vars(Term,V0,V):-
	Term=..[_F|Args],
	extract_vars_list(Args,V0,V).


extract_vars_list([],V,V).

extract_vars_list([Term|T],V0,V):-
	extract_vars(Term,V0,V1),
	extract_vars_list(T,V1,V).

member_eq(A,[H|_T]):-
	A==H,!.

member_eq(A,[_H|T]):-
	member_eq(A,T).

/* auxiliary predicates */
list2or([X],X):-
		X\=;(_,_),!.

list2or([H|T],(H ; Ta)):-!,
		list2or(T,Ta).


list2and([],true):-!.

list2and([X],X):-
		X\=(_,_),!.

list2and([H|T],(H,Ta)):-!,
		list2and(T,Ta).


builtin(_A is _B).
builtin(_A > _B).
builtin(_A < _B).
builtin(_A >= _B).
builtin(_A =< _B).
builtin(_A =:= _B).
builtin(_A =\= _B).
builtin(true).
builtin(false).
builtin(_A = _B).
builtin(_A==_B).
builtin(_A\=_B).
builtin(_A\==_B).
builtin(member(_El,_L)).
builtin(average(_L,_Av)).
builtin(max_list(_L,_Max)).
builtin(min_list(_L,_Max)).


average(L,Av):-
	sum_list(L,Sum),
	length(L,N),
	Av is Sum/N.

/* set(Par,Value) can be used to set the value of a parameter */
set(Parameter,Value):-
	retract(setting(Parameter,_)),
	assert(setting(Parameter,Value)).

:-['metainterprete_sem.pl'].

