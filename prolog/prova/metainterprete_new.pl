%:-use_module(library(trill)).
:-use_module(trill).
 
is_lp_assertion(lpClassAssertion(_,_)).
is_lp_assertion(lpPropertyAssertion(_,_,_)).

lp_assertion_to_atom(lpClassAssertion(Class,Individual),Atom):-
                Atom=..[Class,Individual].
lp_assertion_to_atom(lpPropertyAssertion(Role,Individual1, Individual2),Atom):-
                Atom=..[Role,Individual1,Individual2].
                
isSameIndividual(lpClassAssertion(_,Individual)):-
                Individual=..[sameIndividual|_].
 
solveNewGoals([],_,[]).
solveNewGoals([H|T],G,E):-
                H \= G,
                solvei(H,EH),
                solveNewGoals(T,G,ET),
                append(EH,ET,E).

solve(G) :-
  %retractall(abox(_)),
  retractall(ind(_)),
  build_and_expand(_),
  %assert(abox(A)),
  solvei(G,E),
  list_to_set(E,Ex),
  write(Ex).
 
solvei(true,[]):-!.

% gestione clausole a(X):-b(X,Y),c(Y)
solvei((A,B),E):-
		A=..[R,I,Y],
		B=..[C,Y],
		instanceOf_meta(someValuesFrom(R,C),I,Explanation),
		include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,(A,B),Ex),
                append(Explanation,Ex,E).

solvei((A,B),E):-!,
                solvei(A,EA),
                solvei(B,EB),
                append(EA,EB,E).


solvei(nbf(Goal),['toImplement'|E]):-
                !,
                \+(solvei(Goal),E).
                
solvei(Goal,[(Goal:-Body)|E]):-
                clause(Goal,Body),
                solvei(Body,E).

solvei(Goal,E):-
                Goal=..[Class,Individual],
                instanceOf_meta(Class,Individual,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,Goal,Ex),
                append(Explanation,Ex,E).


solvei(Goal,[subClassOf(SubClass,Class)|E]):-
		Goal=..[Class,Individual],
		owl2_model:subClassOf(SubClass,Class),
		%( atom(SubClass) ->
		%  (NewGoal=..[SubClass,Individual],
                %   solvei(NewGoal)
                %  )
                %  ;
                %  (
                 \+ atom(SubClass),
                   solveii(SubClass,Individual,E).
                %  )
                %).
solvei(Goal,[equivalentClasses(L)|E]):-
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
                   solveii(SubClass,Individual,E).
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
solvei(Goal,E):-
		Goal=..[Role,Individual1,Indovidual2],
		property_value_meta(Role,Individual1,Indovidual2,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,Goal,Ex),
                append(Explanation,Ex,E).

% queste forse saranno da migliorare quando si calcolerà la probabilità
% se infatti dobbiamo calcolare la probabilità di a(X,Y):-b(X,Y) ci sarà da gestire il caso di individui anonimi
% creati dalla exists_rule
%concept for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,E):-
  H=..[C,_],
  clause(H,B),
  B=..[D,_], %% d estendere a clausole con più congiunti nel corpo
  instanceOf_meta(allValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),Ex),
                append(Explanation,Ex,E).

%role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,E):-
  H=..[R,_,_],
  clause(H,B),
  B=..[S,_,_],
  instanceOf_meta(allValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),Ex),
                append(Explanation,Ex,E).
  
%concept and role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,E):-
  H=..[R,_,_],
  clause(H,B),
  B=..[S,_,_],
  H1=..[C,_],
  clause(H1,B1),
  B1=..[D,_],
  instanceOf_meta(allValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),Ex),
                append(Explanation,Ex,E).

%concept for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,E):-
  H=..[C,_],
  clause(H,B),
  B=..[D,_], %% d estendere a clausole con più congiunti nel corpo
  instanceOf_meta(someValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),Ex),
                append(Explanation,Ex,E).

%role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,E):-
  H=..[R,_,_],
  clause(H,B),
  B=..[S,_,_],
  instanceOf_meta(someValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),Ex),
                append(Explanation,Ex,E). 

%concept and role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,E):-
  H=..[R,_,_],
  clause(H,B),
  B=..[S,_,_],
  H1=..[C,_],
  clause(H1,B1),
  B1=..[D,_],
  instanceOf_meta(someValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),Ex),
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
  		(someValuesFrom(a,b) -> clause(a,e) -> risolve il goal somevalues(e,b))
******************************/
