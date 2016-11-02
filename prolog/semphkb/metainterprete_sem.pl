:- use_module('../trill/trill.pl').

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

solve(G,Ex) :-
  %retractall(abox(_)),
  build_and_expand(_),
  %assert(abox(A)),
  solvei(G,[],GS,E),
  list_to_set(E,Ex).
  %write(Ex),nl,
  %write(GS),nl,nl.

solve(G) :-
  solve(G,_).

solvei(true,GS,GS,[]):-!.

solvei(A,GAS,GAS,[]):-
                builtin(A),!,
                call(A).

solvei((A,B),GAS,[B|GS],E):-
                builtin(A),!,
                call(A),
                solvei(B,GAS,GS,E).

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


solvei(nbf(Goal),GAS,GAS,[]):-!,
                \+ solvei(Goal,GAS,_GS,_E).

solvei(\+Goal,GAS,GAS,[]):-!,
                \+ solvei(Goal,GAS,_GS,_E).

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

/*
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
*/
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
		%setof(Expl1,solvei(Goal,GAS,GS,Expl1),Expl)
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
  GAST=[H|GAS],
  ((instanceOf_meta(allValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(allValuesFrom(R,D),I,GAST,GSNG,E)),
  GS=[allValuesFrom(R,D)|GSNG].

% role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  GAST=[H|GAS],
  ((instanceOf_meta(allValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(allValuesFrom(S,C),I,GAST,GSNG,E)),
  GS=[allValuesFrom(S,C)|GSNG].

% concept and role for concepts allValuesFrom
solveii(allValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  H1=..[C,_],
  find_clause(H1,B1,_),
  B1=..[D,_],
  GAST=[H|GAS],
  ((instanceOf_meta(allValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,allValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(allValuesFrom(S,D),I,GAST,GSNG,E)),
  GS=[allValuesFrom(S,D)|GSNG].

% concept for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[C,_],
  find_clause(H,B,_),
  B=..[D,_], %% d estendere a clausole con più congiunti nel corpo
  GAST=[H|GAS],
  ((instanceOf_meta(someValuesFrom(R,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(someValuesFrom(R,D),I,GAST,GSNG,E)),
  GS=[someValuesFrom(R,D)|GSNG].

% role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  GAST=[H|GAS],
  ((instanceOf_meta(someValuesFrom(S,C),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(someValuesFrom(S,C),I,GAST,GSNG,E)),
  GS=[someValuesFrom(S,C)|GSNG].

% concept and role for concepts someValuesFrom
solveii(someValuesFrom(R,C),I,GAS,GS,E):-
  H=..[R,_,_],
  find_clause(H,B,_),
  B=..[S,_,_],
  H1=..[C,_],
  find_clause(H1,B1,_),
  B1=..[D,_],
  GAST=[H|GAS],
  ((instanceOf_meta(someValuesFrom(S,D),I,Explanation),
                include(is_lp_assertion,Explanation,LPAssertions),
                maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                solveNewGoals(Atoms,someValuesFrom(R,C),GAST,GSNG,Ex),
                append(Explanation,Ex,E)
  );
  solveii(someValuesFrom(S,D),I,GAST,GSNG,E)),
  GS=[someValuesFrom(S,D)|GSNG].

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


find_clause(H,B,(H:-B)):-
	rule(H:-B).

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
