:- module(metainterpreter,[prob/2,solve/2,p/1]).

:- use_module('../trill/trill.pl').
:- use_foreign_library(foreign(bddem),install).

:-dynamic rule/8,rule_by_num/5,rule_uniform/8,def_rule/2.

:- style_check(-discontiguous).

:-dynamic setting/2.

setting(epsilon,0.00001).
setting(ground_body,false).

prob(Goal,P) :-
	setof(Expl,find_expl([Goal],Expl),ExplDup),
	compute_prob_mt(ExplDup,P).
	

solve(Goal,E):-
	find_expl([Goal],E).

find_expl(GoalsList,Deriv):-
	build_and_expand(_),
	solve(GoalsList,[],DerivDup,[],_GS),
	sort(DerivDup,Deriv).


/* solve(GoalsList,CIn,COut, GSIn,GSOut) takes a list of goals and an input C set
and returns an output C set
The C set is a list of triple (N,R,S) or predicates trill(G,E) where
- N is the index of the head atom used, starting from 0
- R is the index of the non ground rule used, starting from 1
- S is the substitution of rule R, in the form of a list whose elements
	are of the form 'VarName'=value
- G is the goal of which EX is an explanation
- E is an explanation for goal G returned by trill
The GS set is a list of executed goals
*/

solve([],C,C, GS,GS) :- !.


/* negation, both \+ and nbf/1 are usable */

solve([\+ H |T],CIn,COut, GAS,GS) :- !,
    (member(nbf(H),GAS) -> solve(T,CIn,COut, GAS,GS)
        ;
	(list2and(HL,H),
	 (setof(Expl,solve(HL,[],Expl, GAS,GAS1),CN) -> %% GAS1 da gestire meglio
		append(CIn,[nbf(CN)],C1),
		solve(T,C1,COut, [nbf(H)|GAS1],GS)
	  ;
		((length(HL,1),HL=[ClassHL],ClassHL=..[Class,Individual]) ->
			(solve_trill(complementOf(Class),Individual,T,CIn,COut, GAS,GS) ->
		  		true
		 	 ;
		  		solve(T,CIn,COut, [nbf(H)|GAS],GS)
			)
		 ;
		 	solve(T,CIn,COut, [nbf(H)|GAS],GS)
		)
	 )
	)
    ).

solve([nbf(H)|T],CIn,COut, GAS,GS) :- !,
    (member(nbf(H),GAS) -> solve(T,CIn,COut, GAS,GS)
        ;
	(list2and(HL,H),
	 (setof(Expl,solve(HL,[],Expl, GAS,GAS1),CN) -> %% GAS1 da gestire meglio
		append(CIn,[nbf(CN)],C1),
		solve(T,C1,COut, [nbf(H)|GAS1],GS)
	  ;
		((length(HL,1),HL=[ClassHL],ClassHL=..[Class,Individual]) ->
			(solve_trill(complementOf(Class),Individual,T,CIn,COut, GAS,GS) ->
		  		true
		 	 ;
		  		solve(T,CIn,COut, [nbf(H)|GAS],GS)
			)
		 ;
		 	solve(T,CIn,COut, [nbf(H)|GAS],GS)
		)
	 )
	)
    ).

solve([H|T],CIn,COut, GAS,GS):-
	builtin(H),!,
	call(H),
	solve(T,CIn,COut, GAS,GS).

solve([H|T],CIn,COut, GAS,GS):-
	member(H,GAS) ->
		solve(T,CIn,COut,GAS,GS)
	 ;
		(def_rule(H,B),
		 append(B,T,NG),
		 solve(NG,CIn,COut, GAS,GS)
		).

solve([H|T],CIn,COut, GAS,GS):-
     (member(H,GAS) -> solve(T,CIn,COut,GAS,GS)
       ;
	(find_rule(H,(R,S,N),B,CIn),
	solve_pres(R,S,N,B,T,CIn,COut, [H|GAS],GS)
	)
     ).

/*
solve([A,B|T],CIn,COut, GAS,GS) :-
	A=..[R,I,Y],
	B=..[C,Y],
	solve_trill(someValuesFrom(R,C),I,T,CIn,COut, GAS,GS).


solve([A,B|T],CIn,COut, GAS,GS) :-
	B=..[R,I,Y],
	A=..[C,Y],
	solve_trill(someValuesFrom(R,C),I,T,CIn,COut, GAS,GS).
*/

solve([H|T],CIn,COut, GAS,GS) :-
	H=..[Class,Individual],
	solve_trill(Class,Individual,T,CIn,COut, GAS,GS).

solve([H|T],CIn,COut, GAS,GS) :-
	H=..[Role,Individual1,Individual2],
	solve_trill(Role,Individual1,Individual2,T,CIn,COut, GAS,GS).


solve([H|T],CIn,COut, GAS,GS) :-
	H=..[Class,Individual],
	(member(instanceOf(Class,Individual),GAS) -> solve(T,CIn,COut,GAS,GS)
	 ;
	  (owl2_model:subClassOf(SubClass,Class),
	   append(CIn,[subClassOf(SubClass,Class)],C1),
	   (atom(SubClass) ->
		(SubClassAtom =.. [SubClass,Individual],
		 append([SubClassAtom],T,NG),
		 solve(NG,C1,COut,[instanceOf(Class,Individual)|GAS],GS)
		)
	    ;
	 	solve_not_atomic_concept([(SubClass,Individual)|T],C1,COut,[instanceOf(Class,Individual)|GAS],GS)
	   )
	  )
	).
	


/* **********************
	UTILITIES
   ********************** */

list2or([X],X):-
	X\=;(_,_),!.

list2or([H|T],(H ; Ta)):-!,
	list2or(T,Ta).

list2and([X],X):-
	X\=(_,_),!.

list2and([H|T],(H,Ta)):-!,
	list2and(T,Ta).


member_eq(A,[H|_T]):-
	A==H,!.

member_eq(A,[_H|T]):-
	member_eq(A,T).


/* find_rule(G,(R,S,N),Body,C) takes a goal G and the current C set and
returns the index R of a disjunctive rule resolving with G together with
the index N of the resolving head, the substitution S and the Body of the
rule */
find_rule(H,(R,S,N),Body,_C):-
	rule(H,_P,N,R,S,_,Head,Body),
	member_head(H,Head,0,N).

find_rule(H,(R,S,Number),Body,_C):-
	rule_uniform(H,R,S,_,1/_Num,_L,Number,Body).

member_head(H,[(H:_P)|_T],N,N).

member_head(H,[(_H:_P)|T],NIn,NOut):-
	N1 is NIn+1,
	member_head(H,T,N1,NOut).

not_already_present_with_a_different_head(_N,_R,_S,[]).

not_already_present_with_a_different_head(N,R,S,[nbf(LNeg)|T]):-
	not_already_present_with_a_different_head_in_nbf(N,R,S,LNeg),
	not_already_present_with_a_different_head(N,R,S,T).

not_already_present_with_a_different_head(N,R,S,[(N1,R,S1)|T]):-
	not_different(N,N1,S,S1),!,
	not_already_present_with_a_different_head(N,R,S,T).

not_already_present_with_a_different_head(N,R,S,[(_N1,R1,_S1)|T]):-
	R\==R1,
	not_already_present_with_a_different_head(N,R,S,T).

not_different(_N,_N1,S,S1):-
	S\=S1,!.

not_different(N,N1,S,S1):-
	N\=N1,!,
	dif(S,S1).

not_different(N,N,S,S).

not_already_present_with_a_different_head_in_nbf(_N,_R,_S,[]).

not_already_present_with_a_different_head_in_nbf(N,R,S,[L|T]) :-
	not_already_present_with_a_different_head(N,R,S,L),
	not_already_present_with_a_different_head_in_nbf(N,R,S,T).

solve_pres(R,S,N,B,T,CIn,COut, GAS,GS):-
	member_eq((N,R,S),CIn),!,
	append(B,T,NG),
	solve(NG,CIn,COut, GAS,GS).

solve_pres(R,S,N,B,T,CIn,COut, GAS,GS):-
	append(CIn,[(N,R,S)],C1),
	append(B,T,NG),
	solve(NG,C1,COut, GAS,GS).


/* TRILL utilities */
% solve_trill for classAssertion queries
solve_trill(Class,Individual,T,CIn,COut, GAS,GS) :-
	member(instanceOf(Class,Individual),GAS),
	%member(trill((Class,Individual),_),CIn),
	!,
	solve(T,CIn,COut, GAS,GS).

/*
solve_trill(Class,Individual,T,CIn,COut, GAS,GS) :-
	instanceOf_meta(Class,Individual,Explanation),
	include(is_lp_subsumption,Explanation,LPSubsumptions),
	maplist(lp_subsumption_to_atom,LPSubsumptions,AtomsSub),
	solve_all(AtomsSub,GAS,GAS1,CN),
	include(is_lp_assertion,Explanation,LPAssertions),
        maplist(lp_assertion_to_atom,LPAssertions,Atoms0),
        sort(Atoms0,Atoms),
        append(Atoms,T,NG),
        append(CIn,CN,C0),
        append(C0,[trill((Class,Individual),Explanation)],C1),
        solve(NG,C1,COut, [instanceOf(Class,Individual)|GAS1],GS).
*/

solve_trill(Class,Individual,T,CIn,COut, GAS,GS) :-
	instanceOf_meta(Class,Individual,Explanation0),
	include(is_lp_assertion,Explanation0,LPAssertions),
        maplist(lp_assertion_to_atom,LPAssertions,Atoms),
        %sort(Atoms0,Atoms),
        delete(Explanation0,lpClassAssertion(_,_),Explanation1),
        delete(Explanation1,lpPropertyAssertion(_,_,_),Explanation),
        append(Atoms,T,NG),
        append(CIn,Explanation,C1),
	solve(NG,C1,COut, [instanceOf(Class,Individual)|GAS],GS).

% solve_trill for propertyAssertion queries
solve_trill(Role,Individual1,Individual2,T,CIn,COut, GAS,GS) :-
	member(propertyAssertion(Role,Individual1,Individual2),GAS),
	%member(trill((Role,Individual1,Individual2),_),CIn),
	!,
	solve(T,CIn,COut, GAS,GS).

solve_trill(Role,Individual1,Individual2,T,CIn,COut, GAS,GS) :-
	property_value_meta(Role,Individual1,Individual2,Explanation0),
	include(is_lp_assertion,Explanation0,LPAssertions),
        maplist(lp_assertion_to_atom,LPAssertions,Atoms),
        %sort(Atoms0,Atoms),
        delete(Explanation0,lpClassAssertion(_,_),Explanation1),
        delete(Explanation1,lpPropertyAssertion(_,_,_),Explanation),
        append(Atoms,T,NG),
        append(CIn,Explanation,C1),
        solve(NG,C1,COut, [propertyAssertion(Role,Individual1,Individual2)|GAS],GS).


solve_not_atomic_concept([(someValuesFrom(R,C),Individual)|T],CIn,COut,GAS,GS):-
	Role=..[R,Individual,X],
	Concept=..[C,X],
	append([Role,Concept],T,NG),
	solve(NG,CIn,COut,[instanceOf(someValuesFrom(R,C),Individual)|GAS],GS).

solve_not_atomic_concept([(allValuesFrom(R,C),Individual)|T],CIn,COut,GAS,GS):-
	Role=..[R,Individual,X],
	findall(X,solve(Role,_),LInds),
	create_new_goals(C,LInds,NGInds),
	append(NGInds,T,NG),
	solve(NG,CIn,COut,[instanceOf(someValuesFrom(R,C),Individual)|GAS],GS).
	
solve_not_atomic_concept([(Class,Individual)|T],CIn,COut,GAS,GS):-
	solve_trill(Class,Individual,T,CIn,COut, GAS,GS).

%solve_all([],GAS,GAS,[]).

%solve_all([G|T],GAS,GAS1,ExplTot):-
	%retractall(no_trill(false)),
	%assert(no_trill(lpS)),
	%setof(Expl,solve([G],[],Expl, GAS,GAS0),CN),
	%retractall(no_trill(true)),
	%assert(no_trill(false)),
	%solve_all(T,GAS0,GAS1,ExplT),
	%append(CN,ExplT,ExplTot).

create_new_goals(_C,[],[]).

create_new_goals(C,[H|T],[Goal|T1]):-
	Goal=..[C,H],
	create_new_goals(C,T,T1).


is_lp_assertion(lpClassAssertion(_,_)).
is_lp_assertion(lpPropertyAssertion(_,_,_)).

is_lp_subsumption(lpSubClassOf(_,_)).
is_lp_subsumption(lpSubPropertyOf(_,_)).

lp_assertion_to_atom(lpClassAssertion(Class,Individual),Atom):-
                Atom=..[Class,Individual].
lp_assertion_to_atom(lpPropertyAssertion(Role,Individual1, Individual2),Atom):-
                Atom=..[Role,Individual1,Individual2].

lp_subsumption_to_atom(lpSubClassOf(_,Class),Atom):-
                Atom=..[Class,_Individual].
lp_subsumption_to_atom(lpSubPropertyOf(_,Role),Atom):-
                Atom=..[Role,_Individual1,_Individual2].

find_body(H,B,_CIn,[]) :-
	def_rule(H,Body),
	member(B,Body).

find_body(H,B,CIn,[(R,N,S)]):-
	find_rule(H,(R,S,N),Body,CIn),
	member(B,Body).

/* built-in predicates */
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
builtin(length(_L,_N)).
builtin(member(_El,_L)).
builtin(average(_L,_Av)).
builtin(max_list(_L,_Max)).
builtin(min_list(_L,_Max)).
builtin(nth0(_,_,_)).
builtin(nth(_,_,_)).

average(L,Av):-
	sum_list(L,Sum),
	length(L,N),
	Av is Sum/N.


/* ****************************
	COMPUTING PROB
   **************************** */

:- thread_local
	%get_var_n/5,
        rule_n/1,
        na/2,
        v/3.

compute_prob_mt(Expl,Prob):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  findall(1,owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',_,_),NAnnAss),
  length(NAnnAss,NVarDL),
  count_var(Expl,NVarDL,NV),
  init_test(NV,Env),
  build_bdd_mt(Env,Expl,BDD),
  ret_prob(Env,BDD,Prob),
  end_test(Env), !.



build_bdd_mt(Env,[X],BDD):- !,
  bdd_and_mt(Env,X,BDD).

build_bdd_mt(Env, [H|T],BDD):-
  build_bdd_mt(Env,T,BDDT),
  bdd_and_mt(Env,H,BDDH),
  or(Env,BDDH,BDDT,BDD).

build_bdd_mt(Env,[],BDD):- !,
  zero(Env,BDD).

bdd_and_mt(Env,[],BDDX):- !,
  one(Env,BDDX).

bdd_and_mt(Env,[nbf(Expl)],BDDNeg):-!,
  build_bdd_mt(Env,Expl,BDD2Neg),
  bdd_not(Env,BDD2Neg,BDDNeg).

bdd_and_mt(Env,[trill(_,Expl)],BDD):-!,
  bdd_and_mt(Env,Expl,BDD).


bdd_and_mt(Env,[X],BDDX):-
  get_prob_ax_mt(X,AxN,H,Sub,Prob),!,
  get_var_n(Env,AxN,Sub,Prob,VX),
  equality(Env,VX,H,BDDX),!.

bdd_and_mt(Env,[_X],BDDX):- !,
  one(Env,BDDX).

bdd_and_mt(Env,[nbf(Expl)|T],BDDAnd):-
  build_bdd_mt(Env,Expl,BDD2Neg),
  bdd_not(Env,BDD2Neg,BDDNeg),
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDNeg,BDDT,BDDAnd).

bdd_and_mt(Env,[trill(_,Expl)|T],BDDAnd):-
  bdd_and_mt(Env,Expl,BDDTrill),
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDTrill,BDDT,BDDAnd).

bdd_and_mt(Env,[HA|T],BDDAnd):-
  get_prob_ax_mt(HA,AxN,H,Sub,Prob),!,
  get_var_n(Env,AxN,Sub,Prob,VH),
  equality(Env,VH,H,BDDH),
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).

bdd_and_mt(Env,[_H|T],BDDAnd):- !,
  one(Env,BDDH),
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).


count_var([],C,C).

count_var([D|TD],C0,C1):-
	delete(D,trill(_,_),DCleaned),
	length(DCleaned,NC),
	C2 is C0+NC,
	count_var(TD,C2,C1).

get_var_n(Env,R,S,Probs,V):-
  (
    v(R,S,V) ->
      true
    ;
      length(Probs,L),
      add_var(Env,L,Probs,R,V),
      assert(v(R,S,V))
  ).

get_prob_ax_mt((H,R,Sub),N,H,Sub,Prob) :-
	  rule_by_num(R,_,_,Hs,_),
	  compute_prob_rule(Hs,Prob),
	  ( na(R,N) ->
	      true
	    ;
	      rule_n(N),
	      assert(na(R,N)),
	      retract(rule_n(N)),
	      N1 is N + 1,
	      assert(rule_n(N1))
	  ).


get_prob_ax_mt(Ax,N,0,[],[Prob,ProbN]):-
	Ax \= (_,_,_),
	compute_prob_ax(Ax,Prob),
	ProbN is 1-Prob,
	( na(Ax,N) ->
		true
	 ;
		rule_n(N),
		assert(na(Ax,N)),
		retract(rule_n(N)),
		N1 is N + 1,
		assert(rule_n(N1))
	).

compute_prob_rule([],[]).

compute_prob_rule([(_:P)|T],[P|TP]) :-
	compute_prob_rule(T,TP).


compute_prob_ax(Ax,Prob):-
	findall(ProbA,(owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(ProbAT)),atom_number(ProbAT,ProbA)),Probs),
	compute_prob_ax1(Probs,Prob).


compute_prob_ax1([Prob],Prob):-!.

compute_prob_ax1([Prob1,Prob2],Prob):-!,
  Prob is Prob1+Prob2-(Prob1*Prob2).

compute_prob_ax1([Prob1 | T],Prob):-
  compute_prob_ax1(T,Prob0),
  Prob is Prob1 + Prob0 - (Prob1*Prob0).

/************************/

/* ****************************
	PARSING INPUT FILE
   **************************** */


/* start of predicates for parsing an input file containing a program */

/* p(File) parses the file File.cpl. It can be called more than once without
exiting yap */
p(File):-
	parse(File),!.

parse(File):-
	atom_concat(File,'.cpl',FilePl),
	open(FilePl,read,S),
	read_clauses(S,C),
	close(S),
        retractall(rule_by_num(_,_,_,_,_)),
        retractall(rule(_,_,_,_,_,_,_,_)),
        retractall(def_rule(_,_)),
	retractall(rule_uniform(_,_,_,_,_,_,_,_)),
	trill:add_kb_prefix('disponte','https://sites.google.com/a/unife.it/ml/disponte#'),
	process_clauses(C,1,[]).

process_clauses([(end_of_file,[])],_N,LPList):-!,
	assert_lp_axioms(LPList).

process_clauses([(H,_V)|T],N,LPList):-
	H =.. [kb_prefix,A,B],!,
	trill:add_kb_prefix(A,B),
	process_clauses(T,N,LPList).

process_clauses([(H,_V)|T],N,LPList):-
	H =.. [owl_rdf,String],!,
	owl2_model:parse_rdf_from_owl_rdf_pred(String),
	process_clauses(T,N,LPList).

process_clauses([(H,_V)|T],N,LPList):-
	H =.. [P|Args],
	owl2_model:is_axiom(P),!,
	owl2_model:create_and_assert_axioms(P,Args),
	process_clauses(T,N,LPList).

process_clauses([((H:-B),V)|T],N,LPList):-
	H=uniform(A,P,L),!,
	list2and(BL,B),
	process_body(BL,V,V1),
	remove_vars([P],V1,V2),
	append(BL,[length(L,Tot),nth0(Number,L,P)],BL1),
	append(V2,['Tot'=Tot],V3),
	assertz(rule_by_num(N,V3,_NHN,uniform(A:1/Tot,L,Number),BL1)),
	assertz(rule_uniform(A,N,V3,_NHU,1/Tot,L,Number,BL1)),
	N1 is N+1,
	process_clauses(T,N1,LPList).

process_clauses([((H:-B),V)|T],N,LPList0):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,HL,HLPList),
	list2and(BL,B),
	process_body(BL,V,V1),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,BL,NH,N,V1),
	assertz(rule_by_num(N,V1,NH,HL,BL)),
	N1 is N+1,
	append(LPList0,HLPList,LPList),
	process_clauses(T,N1,LPList).

process_clauses([((H:-B),V)|T],N,LPList0):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,HL,HLPList),
	list2and(BL,B),
	process_body(BL,V,V1),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,BL,NH,N,V1),
	assertz(rule_by_num(N,V1,NH,HL,BL)),
	N1 is N+1,
	append(LPList0,HLPList,LPList),
	process_clauses(T,N1,LPList).

process_clauses([((H:-B),_V)|T],N,LPList0):-!,
	list2and(BL,B),
	assert(def_rule(H,BL)),
	functor(H,Pred,Arity),
	append(LPList0,[Pred/Arity],LPList),
	process_clauses(T,N,LPList).

process_clauses([(H,V)|T],N,LPList0):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,HL,HLPList),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,[],NH,N,V),
	assertz(rule_by_num(N,V,NH,HL,[])),
	N1 is N+1,
	append(LPList0,HLPList,LPList),
	process_clauses(T,N1,LPList).

process_clauses([(H,V)|T],N,LPList0):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,HL,HLPList),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,[],NH,N,V),
	assertz(rule_by_num(N,V,NH,HL,[])),
	N1 is N+1,
	append(LPList0,HLPList,LPList),
	process_clauses(T,N1,LPList).

process_clauses([(H,_V)|T],N,LPList0):-
	assert(def_rule(H,[])),
	functor(H,Pred,Arity),
	append(LPList0,[Pred/Arity],LPList),
	process_clauses(T,N,LPList).


assert_rules([],_Pos,_HL,_BL,_Nh,_N,_V1):-!.

assert_rules(['':_P],_Pos,_HL,_BL,_Nh,_N,_V1):-!.

assert_rules([H:P|T],Pos,HL,BL,NH,N,V1):-
	assertz(rule(H,P,Pos,N,V1,NH,HL,BL)),
	Pos1 is Pos+1,
	assert_rules(T,Pos1,HL,BL,NH,N,V1).

/* asserts lpClassAssertion and lpPropertyAssertion following the clauses */
/* PER TUTTE O DEVO CONTROLLARE CHE SIANO SOLO a(X):-b(X). r(X,Y):-s(X,Y).???? */
assert_lp_axioms([]).

assert_lp_axioms([P/1|T]):- !,
	owl2_model:create_and_assert_axioms(lpClassAssertion,[P]),
	assert_lp_axioms(T).

assert_lp_axioms([P/2|T]):- !,
	owl2_model:create_and_assert_axioms(lpPropertyAssertion,[P]),
	assert_lp_axioms(T).

assert_lp_axioms([_P/_A|T]):-
	assert_lp_axioms(T).


/* if the annotation in the head are not ground, the null atom is not added
and the eventual formulas are not evaluated */

process_head(HL,NHL,LPList):-
	(ground_prob(HL)->
		process_head_ground(HL,0,NHL,LPList)
	;
		NHL=HL,LPList=[]
	).

ground_prob([]).

ground_prob([_H:PH|T]):-
	ground(PH),
	ground_prob(T).

process_head_ground([H:PH],P,[H:PH1|Null],[Pred/Arity]):-
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

process_head_ground([H:PH|T],P,[H:PH1|NT],[Pred/Arity|LPList]):-
	PH1 is PH,
	P1 is P+PH1,
	functor(H,Pred,Arity),
	process_head_ground(T,P1,NT,LPList).

/* setof must have a goal of the form B^G where B is a term containing the existential variables */
process_body([],V,V).

process_body([setof(A,B^_G,_L)|T],VIn,VOut):-!,
	get_var(A,VA),
	get_var(B,VB),
	remove_vars(VA,VIn,V1),
	remove_vars(VB,V1,V2),
	process_body(T,V2,VOut).

process_body([setof(A,_G,_L)|T],VIn,VOut):-!,
	get_var(A,VA),
	remove_vars(VA,VIn,V1),
	process_body(T,V1,VOut).

process_body([bagof(A,B^_G,_L)|T],VIn,VOut):-!,
	get_var(A,VA),
	get_var(B,VB),
	remove_vars(VA,VIn,V1),
	remove_vars(VB,V1,V2),
	process_body(T,V2,VOut).

process_body([bagof(A,_G,_L)|T],VIn,VOut):-!,
	get_var(A,VA),
	remove_vars(VA,VIn,V1),
	process_body(T,V1,VOut).

process_body([_H|T],VIn,VOut):-!,
	process_body(T,VIn,VOut).

get_var_list([],[]).

get_var_list([H|T],[H|T1]):-
	var(H),!,
	get_var_list(T,T1).

get_var_list([H|T],VarOut):-!,
	get_var(H,Var),
	append(Var,T1,VarOut),
	get_var_list(T,T1).

get_var(A,[A]):-
	var(A),!.

get_var(A,V):-
	A=..[_F|Args],
	get_var_list(Args,V).

remove_vars([],V,V).

remove_vars([H|T],VIn,VOut):-
	delete_var(H,VIn,V1),
	remove_vars(T,V1,VOut).

delete_var(_H,[],[]).

delete_var(V,[VN=Var|T],[VN=Var|T1]):-
	V\==Var,!,
	delete_var(V,T,T1).

delete_var(_V,[_H|T],T).

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


listN(N,N,[]):-!.

listN(NIn,N,[NIn|T]):-
	N1 is NIn+1,
	listN(N1,N,T).
/* end of predicates for parsing an input file containing a program */

