:- use_module('../trill/trill.pl').

:- style_check(-discontiguous).



solve(G,Ex) :-
	build_and_expand(_),
	solvei(G,[],_GS,E),
	list_to_set(E,Ex).
  
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
/*
solvei((A,B),GAS,GS,E):-
		A=..[R,I,Y],
		B=..[C,Y],
		instanceOf_meta(someValuesFrom(R,C),I,Explanation),
		   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,(A,B),GAS,GSNG,Ex),
                   GS = [someValuesFrom(R,C)|GSNG],
                append(Explanation,Ex,E).
*/

solvei((A,B),GAS,[B|GS],E):-!,
                solvei(A,GAS,GSA,EA),
                solvei(B,GSA,GS,EB),
                append(EA,EB,E).


solvei(nbf(Goal),GAS,GS,E):-!,
                (member(nbf(Goal),GAS) ->
                   GS = GAS, E = []
                 ;
                   solve_neg(Goal,GAS,GS,E)
		).

solvei(\+Goal,GAS,GS,E):-!,
                (member(nbf(Goal),GAS) ->
                   GS = GAS, E = []
                 ;
                   solve_neg(Goal,GAS,GS,E)
                ).

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
                (member(instanceOf(Class,Individual),GAS) ->
                  GS = GAS, E = []
                 ;
                  (Goal=..[Class,Individual],
                   instanceOf_meta(Class,Individual,Explanation),
                   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,Goal,GAS,GSNG,Ex),
                   GS=[instanceOf(Class,Individual)|GSNG],
                   append(Explanation,Ex,E)
                  )
                ).

solvei(Goal,GAS,GS,E):-
		Goal=..[Role,Individual1,Individual2],
		(member(propertyAssertion(Role,Individual1,Individual2),GAS) ->
		  GS=GAS, E=[]
		 ;
		  (property_value_meta(Role,Individual1,Individual2,Explanation),
                   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,Goal,GAS,GSNG,Ex),
                   GS=[propertyAssertion(Role,Individual1,Individual2)|GSNG],
                   append(Explanation,Ex,E)
                  )
                ).

/*
solvei(Goal,GAS,GS,E):-
		Goal=..[Class,Individual],
		(member(instanceOf(Class,Individual),GAS) -> 
		   GS = GAS, E = []
		  ;
		   (find_subclass(SubClass,Class,Ex0),
		    (atom(SubClass) ->
		       (SubClassAtom=..[SubClass,Individual],
		        solvei(SubClassAtom,[instanceOf(Class,Individual)|GAS],GS,Ex),
		        E=[Ex0|Ex]
		       )
		     ;
		       (solve_not_atomic_concept((SubClass,Individual),[instanceOf(Class,Individual)|GAS],GS,Ex),
		        E=[Ex0|Ex]
		       )
		    )
		   )
		 ).
*/

/* **	MORE COMPLETED VERSION
	SOLVE complementOf WITH TRILL USELESS
solve_neg(Goal,GAS,GS,E) :-
		%setof(Expl1,solvei(Goal,GAS,GS,Expl1),Expl)
		solvei(Goal,GAS,GS,_Expl) *->
		  fail
		 ;
		  (Goal=..[Class,Individual] ->
		  	((member(instanceOf(complementOf(Class),Individual),GAS) ->
                  		GS = GAS, E = []
                  	  ;
                  	  	(instanceOf_meta(complementOf(Class),Individual,Explanation),
                   		 include(is_lp_assertion,Explanation,LPAssertions),
                   		 maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   		 solveNewGoals(Atoms,Goal,GAS,GSNG,Ex),
                   		 GS=[instanceOf(Class,Individual)|GSNG],
                   		 append(Explanation,Ex,E)
                   		)
                   	 ) ->
                   	   true
                   	 ;
                   	   E = [], GS = [nbf(Goal)|GAS]
                   	)   
                    ;
                    	E = [], GS = [nbf(Goal)|GAS]
                   ).                   
*/
solve_neg(Goal,GAS,GS,E) :-
		%setof(Expl1,solvei(Goal,GAS,GS,Expl1),Expl)
		(solvei(Goal,GAS,_GS,_Expl) *->
		  fail
		 ;
		  (E = [], GS = GAS)
		).

solve_not_atomic_concept((someValuesFrom(R,C),Individual),GAS,GS,E):-
	Role=..[R,Individual,X],
	Concept=..[C,X],
	solvei((Role,Concept),[instanceOf(someValuesFrom(R,C),Individual)|GAS],GS,E).

solve_not_atomic_concept((allValuesFrom(R,C),Individual),GAS,GS,E):-
	Role=..[R,Individual,X],
	findall(X,solve(Role,_),LInds),
	create_new_goals(C,LInds,NG),
	solvei(NG,[instanceOf(someValuesFrom(R,C),Individual)|GAS],GS,E).
	
solve_not_atomic_concept((Class,Individual),GAS,GS,E):-
	member(instanceOf(Class,Individual),GAS) ->
                  GS = GAS, E = []
                 ;
                  (instanceOf_meta(Class,Individual,Explanation),
                   include(is_lp_assertion,Explanation,LPAssertions),
                   maplist(lp_assertion_to_atom,LPAssertions,Atoms),
                   solveNewGoals(Atoms,dummyGoal,GAS,GSNG,Ex),
                   GS=[instanceOf(Class,Individual)|GSNG],
                   append(Explanation,Ex,E)
                  ).

create_new_goals(C,[H],Goal):- !,
	Goal=..[C,H].

create_new_goals(C,[H|T],(Goal,T1)):-
	Goal=..[C,H],
	create_new_goals(C,T,T1).

/* **********************
	UTILITIES
   ********************** */

find_clause(H,B,(H:-B)):-
	rule(H:-B).

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

find_subclass(SubClass,Class,subClassOf(SubClass,Class)):-
    owl2_model:subClassOf(SubClass,Class).

find_subclass(SubClass,Class,equivalentClasses(SubClass,Class)):-
    owl2_model:equivalentClasses(L),
    member(Class,L),
    member(SubClass,L).


/* TRILL utilities */
is_lp_assertion(lpClassAssertion(_,_)).
is_lp_assertion(lpPropertyAssertion(_,_,_)).

lp_assertion_to_atom(lpClassAssertion(Class,Individual),Atom):-
                Atom=..[Class,Individual].
lp_assertion_to_atom(lpPropertyAssertion(Role,Individual1, Individual2),Atom):-
                Atom=..[Role,Individual1,Individual2].

%isSameIndividual(lpClassAssertion(_,Individual)):-
%                Individual=..[sameIndividual|_].

solveNewGoals([],_,GS,GS,[]).
solveNewGoals([H|T],G,GAS,GS,E):-
                H \= G,
                solvei(H,GAS,GSH,EH),
                solveNewGoals(T,G,GSH,GS,ET),
                append(EH,ET,E).

