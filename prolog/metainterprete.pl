#:-use_module(library(trill)).
:-use_module(trill).
 
is_lp_class_assertion(lpClassAssertion(_,_)).
lp_class_assertion_to_atom(lpClassAssertion(Class,Individual),Atom):-
                Atom=..[Class,Individual].
isSameIndividual(lpClassAssertion(_,Individual)):-
                Individual=..[sameIndividual|_].
 
solveNewGoals([],_).
solveNewGoals([H|T],G):-
                H \= G,
                solve(H),
                solveNewGoals(T,G).
 
solve(true).
solve((A,B)):-
                solve(A),
                solve(B).
solve(nbf(Goal)):-
                !,
                \+(solve(Goal)).
solve(Goal):-
                clause(Goal,Body),
                solve(Body).
solve(Goal):-
                Goal=..[Class,Individual],
                trill:instanceOf(Class,Individual,Explanation),
                include(is_lp_class_assertion,Explanation,LPClassAssertions),
                maplist(lp_class_assertion_to_atom,LPClassAssertions,Atoms),
                solveNewGoals(Atoms,Goal).
