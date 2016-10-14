%:-use_module(library(trill)).
:-use_module(trill).
:- use_foreign_library(foreign(bddem),install).

:-dynamic rule/8,rule_by_num/5,rule_uniform/8,def_rule/2.

:- style_check(-discontiguous).

 
is_lp_assertion(lpClassAssertion(_,_)).
is_lp_assertion(lpPropertyAssertion(_,_,_)).

lp_assertion_to_atom(lpClassAssertion(Class,Individual),Atom):-
                Atom=..[Class,Individual].
lp_assertion_to_atom(lpPropertyAssertion(Role,Individual1, Individual2),Atom):-
                Atom=..[Role,Individual1,Individual2].
                
isSameIndividual(lpClassAssertion(_,Individual)):-
                Individual=..[sameIndividual|_].
 
solveNewGoals([],_,GS,GS,[]).
solveNewGoals([H|T],G,GAS,GS,E):-
                H \= G,
                solvei(H,GAS,GSH,EH),
                solveNewGoals(T,G,GSH,GS,ET),
                append(EH,ET,E).

prob(G,Prob) :-
 findall(Ex,solve(G,Ex),Expl),%trace,
 compute_prob(Expl,Prob).

solve(G,Ex) :-
  %retractall(abox(_)),
  retractall(ind(_)),
  build_and_expand(_),
  %assert(abox(A)),
  solvei(G,[],GS,E),
  list_to_set(E,Ex),
  write(Ex),nl,
  write(GS),nl,nl.

solve(G) :-
  solve(G,_).
 
solvei(true,GS,GS,[]):-!.

% gestione clausole a(X):-b(X,Y),c(Y)
solvei((A,B),GAS,GS,E):-
		A=..[R,I,Y],
		B=..[C,Y],
		instanceOf_meta(someValuesFrom(R,C),I,Explanation),
		   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,(A,B),GAS,GSNG,Ex),
                   GS = [someValuesFrom(R,C)|GSNG],
                append(Explanation,Ex,E).

solvei((A,B),GAS,[B|GS],E):-!,
                solvei(A,GAS,GSA,EA),
                solvei(B,[A|GSA],GS,EB),
                append(EA,EB,E).


solvei(nbf(Goal),GAS,GS,E):-
                !,
                member(nbf(Goal),GAS) ->
                   GS = GAS, E = []
                 ;
                   solve_neg(Goal,GAS,GS,E).

solvei(Goal,GAS,GS,E):-
                member(Goal,GAS) ->
                  GS=GAS,E=[]
                 ;
                  (find_clause(Goal,Body,Ex0),
                   solvei(Body,[Goal|GAS],GS,Ex),
                   E = [Ex0|Ex]
                  ).

solvei(Goal,GAS,GS,E):-
                Goal=..[Class,Individual],
                member(instanceOf(Class,Individual),GAS) ->
                  GS = GAS, E = []
                 ;
                  (Goal=..[Class,Individual],
                   instanceOf_meta(Class,Individual,Explanation),
                   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,Goal,GAS,GSNG,Ex),
                   GS=[instanceOf(Class,Individual)|GSNG]
                ),
                append(Explanation,Ex,E).


solvei(Goal,GAS,GS,[subClassOf(SubClass,Class)|E]):-
		Goal=..[Class,Individual],
		owl2_model:subClassOf(SubClass,Class),
		%( atom(SubClass) ->
		%  (NewGoal=..[SubClass,Individual],
                %   solvei(NewGoal)
                %  )
                %  ;
                %  (
                 \+ atom(SubClass),
                   solveii(SubClass,Individual,GAS,GSI,E),
                   GS = [subClassOf(SubClass,Class)|GSI].
                %  )
                %).
solvei(Goal,GAS,GS,[equivalentClasses(L)|E]):-
		Goal=..[Class,Individual],
		owl2_model:equivalentClasses(L),
		member(Class,L),
		member(SubClass,L),
		%( atom(SubClass) ->
		%  (dif(Class,SubClass),
                %   NewGoal=..[SubClass,Individual],
                %   solvei(NewGoal)
                %  )
                %  ;
                %  (
                  \+ atom(SubClass),
                   solveii(SubClass,Individual,GAS,GSI,E),
                   GS = [equivalentClasses(L)|GSI].
                %  )
                %). 

/*
solvei(Goal):-
		Goal=..[Prop,I1,I2],
		owl2_model:subPropertyOf(SubProp,Prop),
		atom(SubProp),
                NewGoal=..[SubProp,I1,I2],
                solvei(NewGoal). 
solvei(Goal):-
		Goal=..[Prop,I1,I2],
		owl2_model:equivalentProperties(L),
		member(Prop,L),
		member(SubProp,L),
		atom(SubProp),
		dif(Prop,SubProp),
                NewGoal=..[SubProp,I1,I2],
                solvei(NewGoal). 
*/
solvei(Goal,GAS,GS,E):-
		Goal=..[Role,Individual1,Indovidual2],
		property_value_meta(Role,Individual1,Indovidual2,Explanation),
                   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,Goal,GAS,GSNG,Ex),
                   GS=[propertyAssertion(Role,Individual1,Indovidual2)|GSNG],
                append(Explanation,Ex,E).


solve_neg(Goal,GAS,GS,E) :-
		solvei(Goal,GAS,GS,Expl) *-> 
		  E = [nbf(Expl)]
		 ;
		  E = [], GS = GAS.
                  
%solve_neg(Goal,GAS,GS,[]) :-
%		\+ (solvei(Goal,GAS,GS,_E)).


% queste forse saranno da migliorare quando si calcolerà la probabilità
% se infatti dobbiamo calcolare la probabilità di a(X,Y):-b(X,Y) ci sarà da gestire il caso di individui anonimi
% creati dalla exists_rule
% concept for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,GAS,GS,E):-
  H=..[C,_],
  find_clause(H,B,_),
  B=..[D,_], %% d estendere a clausole con più congiunti nel corpo
  instanceOf_meta(allValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[allValuesFrom(R,D)|GSNG],
  append(Explanation,Ex,E).

% role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  instanceOf_meta(allValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[allValuesFrom(S,C)|GSNG],
  append(Explanation,Ex,E).
  
% concept and role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  H1=..[C,_],
  find_clause(H1,B1,_),
  B1=..[D,_],
  instanceOf_meta(allValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[allValuesFrom(S,D)|GSNG],
  append(Explanation,Ex,E).

% concept for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[C,_],
  find_clause(H,B,_),
  B=..[D,_], %% d estendere a clausole con più congiunti nel corpo
  instanceOf_meta(someValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[someValuesFrom(R,D)|GSNG],
  append(Explanation,Ex,E).

% role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  instanceOf_meta(someValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[someValuesFrom(S,C)|GSNG],
  append(Explanation,Ex,E). 

% concept and role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  H1=..[C,_],
  find_clause(H1,B1,_),
  B1=..[D,_],
  instanceOf_meta(someValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAS,GSNG,Ex),
                GS=[someValuesFrom(S,D)|GSNG],
  append(Explanation,Ex,E).
                
/*****************************
  IDEA:
  - creazione ed espansione abox completa.
  - il meta interprete prende il goal e cerca di risolverlo nel seguente ordine:
  	1. usando LP
  	2. usando trill (le abox create vengono salvate per usarle dopo) 
  	3. cercando subClassOf e equivalentClasses per andare da super a sub class (anche per property)
  		devo eseguire il goal a(c) -> cerco subClassOf(b,a) -> eseguo goal b(c)
  	4. espandere eventuali concetti complessi usando regole prolog clause/2
  		(someValuesFrom(a,b) -> find_clause(a,e) -> risolve il goal somevalues(e,b))
******************************/


find_clause(H,B,(H,B)):-
	def_rule(H,BL),
	list2and(BL,B).

find_clause(H,B,(R,N,S)):-
	find_rule(H,(R,S,N),Body,_),
	list2and(Body,B).

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


/* rem_dup_lists removes the C sets that are a superset of 
another C sets further on in the list of C sets */
rem_dup_lists([],L,L).

rem_dup_lists([H|T],L0,L):-
	(member_subset(H,T);member_subset(H,L0)),!,
	rem_dup_lists(T,L0,L).

rem_dup_lists([H|T],L0,L):-
	rem_dup_lists(T,[H|L0],L).
	
member_subset(E,[H|_T]):-
	subset_my(H,E),!.

member_subset(E,[_H|T]):-
	member_subset(E,T).

subset_my([],_).

subset_my([H|T],L):-
	member_eq(H,L),
	subset_my(T,L).
	
member_eq(A,[H|_T]):-
	A==H,!.
	
member_eq(A,[_H|T]):-
	member_eq(A,T).


/* choose_clauses(CIn,LC,COut) takes as input the current C set and 
the set of C sets for a negative goal and returns a new C set that 
excludes all the derivations for the negative goals */
choose_clauses(C,[],C).

choose_clauses(CIn,[D|T],COut):-
	member((N,R,S),D),
	already_present_with_a_different_head(N,R,S,CIn),!,
	choose_a_head(N,R,S,CIn,C1),
	choose_clauses(C1,T,COut).

	
choose_clauses(CIn,[D|T],COut):-
	member((N,R,S),D),
	new_head(N,R,S,N1),
	\+ already_present(N1,R,S,CIn),
	impose_dif_cons(R,S,CIn),
	choose_clauses([(N1,R,S)|CIn],T,COut).


/* case 1 of Select: a more general rule is present in C with
a different head, instantiate it */
choose_a_head(N,R,S,[(NH,R,SH)|T],[(NH,R,SH)|T]):-
	S=SH, 
	dif(N,NH).

/* case 2 of Select: a more general rule is present in C with
a different head, ensure that they do not generate the same
ground clause */
choose_a_head(N,R,S,[(NH,R,SH)|T],[(NH,R,S),(NH,R,SH)|T]):-
	\+ \+ S=SH, S\==SH, 
	dif(N,NH),
	dif(S,SH).

choose_a_head(N,R,S,[H|T],[H|T1]):-
	choose_a_head(N,R,S,T,T1).


/* select a head different from N for rule R with
substitution S, return it in N1 */
new_head(N,R,S,N1):-
	rule_by_num(R,S,Numbers,Head,_Body),
	Head\=uniform(_,_,_),!,
	nth0(N, Numbers, _Elem, Rest),
	member(N1,Rest).

new_head(N,R,S,N1):-
	rule_by_num(R,S,Numbers,uniform(_A:1/Tot,_L,_Number),_Body),
	listN(0,Tot,Numbers),
	nth0(N, Numbers, _Elem, Rest),
	member(N1,Rest).

already_present_with_a_different_head(N,R,S,[(NH,R,SH)|_T]):-
	\+ \+ S=SH,NH \= N.

already_present_with_a_different_head(N,R,S,[_H|T]):-
	already_present_with_a_different_head(N,R,S,T).


/* checks that a rule R with head N and selection S is already
present in C (or a generalization of it is in C) */ 
already_present(N,R,S,[(N,R,SH)|_T]):-
	S=SH.

already_present(N,R,S,[_H|T]):-
	already_present(N,R,S,T).

impose_dif_cons(_R,_S,[]):-!.

impose_dif_cons(R,S,[(_NH,R,SH)|T]):-!,
	dif(S,SH),
	impose_dif_cons(R,S,T).

impose_dif_cons(R,S,[_H|T]):-
	impose_dif_cons(R,S,T).


/* find_rule(G,(R,S,N),Body,C) takes a goal G and the current C set and
returns the index R of a disjunctive rule resolving with G together with
the index N of the resolving head, the substitution S and the Body of the 
rule */
find_rule(H,(R,S,N),Body,_C):-
	rule(H,_P,N,R,S,_,Head,Body),
	member_head(H,Head,0,N). %,
	%not_already_present_with_a_different_head(N,R,S,C).

find_rule(H,(R,S,Number),Body,_C):-
	rule_uniform(H,R,S,_,1/_Num,_L,Number,Body). %,
	%not_already_present_with_a_different_head(Number,R,S,C).

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


count_var([],C,C).

count_var([D|TD],C0,C1):-
	length(D,NC),
	C2 is C0+NC,
	count_var(TD,C2,C1).

build_formula([],[],Var,Var,C,C).

build_formula([D|TD],[F|TF],VarIn,VarOut,C0,C1):-
	length(D,NC),
	C2 is C0+NC,
	build_term(D,F,VarIn,Var1),
	build_formula(TD,TF,Var1,VarOut,C2,C1).

build_term([],[],Var,Var).

build_term([(_,pruned,_)|TC],TF,VarIn,VarOut):-!,
	build_term(TC,TF,VarIn,VarOut).

build_term([(N,R,S)|TC],[[NVar,N]|TF],VarIn,VarOut):-
	(nth0_eq(0,NVar,VarIn,(R,S))->
		Var1=VarIn
	;
		append(VarIn,[(R,S)],Var1),
		length(VarIn,NVar)
	),
	build_term(TC,TF,Var1,VarOut).

/* nth0_eq(PosIn,PosOut,List,El) takes as input a List,
an element El and an initial position PosIn and returns in PosOut
the position in the List that contains an element exactly equal to El
*/
nth0_eq(N,N,[H|_T],El):-
	H==El,!.

nth0_eq(NIn,NOut,[_H|T],El):-
	N1 is NIn+1,
	nth0_eq(N1,NOut,T,El).

var2numbers([],_N,[]).

var2numbers([(R,S)|T],N,[[N,ValNumber,Probs]|TNV]):-
	find_probs(R,S,Probs),
	length(Probs,ValNumber),
	N1 is N+1,
	var2numbers(T,N1,TNV).

find_probs(R,S,Probs):-
	rule_by_num(R,S,_N,Head,_Body),
	get_probs(Head,Probs).
	
get_probs(uniform(_A:1/Num,_P,_Number),ListP):-
	Prob is 1/Num,
	list_el(Num,Prob,ListP).

get_probs([],[]).

get_probs([_H:P|T],[P1|T1]):-
	P1 is P,
	get_probs(T,T1).

/* ****************************
	PARSING INPUT FILE
   **************************** */


/* start of predicates for parsing an input file containing a program */

/* p(File) parses the file File.cpl. It can be called more than once without 
exiting yap */
p(File):-
	parse(File).

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
	process_clauses(C,1).

process_clauses([(end_of_file,[])],_N):-!.

process_clauses([(H,_V)|T],N):-
	H =.. [kb_prefix,A,B],!,
	trill:add_kb_prefix(A,B),
	process_clauses(T,N).

process_clauses([(H,_V)|T],N):-
	H =.. [owl_rdf,String],!,
	owl2_model:parse_rdf_from_owl_rdf_pred(String),
	process_clauses(T,N).

process_clauses([(H,_V)|T],N):-
	H =.. [P|Args],
	member(P,[class,datatype,objectProperty,dataProperty,annotationProperty,namedIndividual,subClassOf,equivalentClasses,disjointClasses,disjointUnion,subPropertyOf,equivalentProperties,
	disjointProperties,inverseProperties,propertyDomain,propertyRange,functionalProperty,inverseFunctionalProperty,reflexiveProperty,irreflexiveProperty,symmetricProperty,asymmetricProperty,
	transitiveProperty,hasKey,sameIndividual,differentIndividuals,classAssertion,propertyAssertion,negativePropertyAssertion,annotationAssertion,
	lpClassAssertion,lpPropertyAssertion]),!,
	owl2_model:create_and_assert_axioms(P,Args),
	process_clauses(T,N).


process_clauses([((H:-B),V)|T],N):-
	H=uniform(A,P,L),!,
	list2and(BL,B),
	process_body(BL,V,V1),
	remove_vars([P],V1,V2),
	append(BL,[length(L,Tot),nth0(Number,L,P)],BL1),
	append(V2,['Tot'=Tot],V3),
	assertz(rule_by_num(N,V3,_NHN,uniform(A:1/Tot,L,Number),BL1)),
	assertz(rule_uniform(A,N,V3,_NHU,1/Tot,L,Number,BL1)),
	N1 is N+1,
	process_clauses(T,N1).

process_clauses([((H:-B),V)|T],N):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,HL),
	list2and(BL,B),
	process_body(BL,V,V1),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,BL,NH,N,V1),
	assertz(rule_by_num(N,V1,NH,HL,BL)),
	N1 is N+1,
	process_clauses(T,N1).

process_clauses([((H:-B),V)|T],N):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,HL),
	list2and(BL,B),
	process_body(BL,V,V1),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,BL,NH,N,V1),
	assertz(rule_by_num(N,V1,NH,HL,BL)),
	N1 is N+1,
	process_clauses(T,N1).
	
process_clauses([((H:-B),_V)|T],N):-!,
	list2and(BL,B),
	assert(def_rule(H,BL)),
	process_clauses(T,N).

process_clauses([(H,V)|T],N):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,HL),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,[],NH,N,V),
	assertz(rule_by_num(N,V,NH,HL,[])),
	N1 is N+1,
	process_clauses(T,N1).

process_clauses([(H,V)|T],N):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,HL),
	length(HL,LH),
	listN(0,LH,NH),
	assert_rules(HL,0,HL,[],NH,N,V),
	assertz(rule_by_num(N,V,NH,HL,[])),
	N1 is N+1,
	process_clauses(T,N1).
	
process_clauses([(H,_V)|T],N):-
	assert(def_rule(H,[])),
	process_clauses(T,N).


assert_rules([],_Pos,_HL,_BL,_Nh,_N,_V1):-!.

assert_rules(['':_P],_Pos,_HL,_BL,_Nh,_N,_V1):-!.

assert_rules([H:P|T],Pos,HL,BL,NH,N,V1):-
	assertz(rule(H,P,Pos,N,V1,NH,HL,BL)),
	Pos1 is Pos+1,
	assert_rules(T,Pos1,HL,BL,NH,N,V1).


/* if the annotation in the head are not ground, the null atom is not added
and the eventual formulas are not evaluated */
	
process_head(HL,NHL):-
	(ground_prob(HL)->
		process_head_ground(HL,0,NHL)
	;
		NHL=HL
	).

ground_prob([]).

ground_prob([_H:PH|T]):-
	ground(PH),
	ground_prob(T).

process_head_ground([H:PH],P,[H:PH1|Null]):-
	PH1 is PH,
	PNull is 1-P-PH1,
	%setting(epsilon_parsing,Eps),
	Eps = 0.00001,
	EpsNeg is - Eps,
	PNull > EpsNeg,
	(PNull>Eps->
		Null=['':PNull]
	;
		Null=[]
	).

process_head_ground([H:PH|T],P,[H:PH1|NT]):-
	PH1 is PH,
	P1 is P+PH1,
	process_head_ground(T,P1,NT).

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
read_clauses(S,Clauses):-
	%(setting(ground_body,true)->
		read_clauses_ground_body(S,Clauses).
	%;
	%	read_clauses_exist_body(S,Clauses)
	%).


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


extract_vars_cl(end_of_file,[]).

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


/* ****************************
	COMPUTING PROB
   **************************** */

:- thread_local 
	%get_var_n/5,
        rule_n/1,
        na/2,
        v/3.
   
compute_prob(Expl,Prob):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  %trill:get_trill_current_module(Name),
  findall(1,owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',_,_),NAnnAss),
  length(NAnnAss,NVarDL),
  count_var(Expl,NVarDL,NV),
  %NV = NVarLPAD, %
  %NV is NVarDL + NVarLPAD,
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
  get_var_n(Env,AxN,Sub,Prob,VH), % axN controllo solo la regola, no lista vuota ma sostituzione, lista prob con tutte le prob
  equality(Env,VH,H,BDDH), % no 0 ma la testa
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).
  
bdd_and_mt(Env,[_H|T],BDDAnd):- !,
  one(Env,BDDH),
  bdd_and_mt(Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).



 
get_var_n(Env,R,S,Probs,V):-
  ( 
    v(R,S,V) -> 
      true
    ; 
      length(Probs,L),
      add_var(Env,L,Probs,R,V),
      assert(v(R,S,V))
  ).

get_prob_ax_mt((H,R,Sub),N,H,Sub,Prob) :-%trace,
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

/*
get_prob_ax_mt((Ax,_Ind),N,0,[],[Prob,ProbN]):- !,
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
*/
  
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
	%trill:get_trill_current_module(Name),
	findall(ProbA,(owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(ProbAT)),atom_number(ProbAT,ProbA)),Probs),
	compute_prob_ax1(Probs,Prob).

 
compute_prob_ax1([Prob],Prob):-!.

compute_prob_ax1([Prob1,Prob2],Prob):-!,
  Prob is Prob1+Prob2-(Prob1*Prob2).
  
compute_prob_ax1([Prob1 | T],Prob):-
  compute_prob_ax1(T,Prob0),
  Prob is Prob1 + Prob0 - (Prob1*Prob0).  

/************************/

