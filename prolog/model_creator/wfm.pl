:-use_module(library(apply)).
:-use_module(library(lambda)).
:-use_module(trill).

rules(e1,[rule(p(a),[not(d(a)),o(a)]),
       rule(p(b),[not(d(b)),o(b)]),
       rule(e(a),[not(e(a)),o(a)]),
       rule(e(b),[not(e(b)),o(b)]),
       rule(o(b),[]),
       rule(o(a),[])]).
axioms(e1,[classAssertion(c,b),subClassOf(c,d),equivalentClasses([c,complementOf(e)])]).

rules(e2,[rule(p(a),[not(p(a))]),
       rule(q(a),[]),
       rule(r(a),[not(r(a))])]).
axioms(e2,[subClassOf(q,complementOf(r))]).

rules(e3,[rule(exp(tts),[]),
	 rule(rec(tts),[cd(tts),not(owns(tts)),not(lowEval(tts)),int(tts)]),
	 rule(int(tts),[])]).
axioms(e3,[subClassOf(exp,complementOf(rec)),classAssertion(cd,tts)]).

removeNegations([],_,[]).
removeNegations([not(A)|_],S,_):-
	member(A,S),
	!,
	fail.
removeNegations([not(_)|T],S,B):-
	!,
	removeNegations(T,S,B).
removeNegations([H|T],S,[H|B]):-
	removeNegations(T,S,B).

minMod(kb(O,P),KA,M):-
	minMod(kb(O,P),KA,[],M).
minMod(KB,KA,S,M):-
	t(KB,KA,S,M1),(
	subset(M1,S)->
	    S=M;
	    minMod(KB,KA,M1,M)).


gamma(kb(O,P),KA,S,S2):-
	findall(rule(Head,Body1),
		(   member(rule(Head,Body),P),
		    removeNegations(Body,S,Body1)
		),
		P1),
	minMod(kb(O,P1),KA,S2).
gammaPrime(kb(O,P),KA,S,S2):-
	findall(rule(Head,Body1),
		(   member(rule(Head,Body),P),
		    removeNegations(Body,S,Body1)
		),
		P1),
	dl_models(O,S,A),
	findall(N,member(neg(N),A),Ns),
	include(\Rule^(Rule=rule(H,_),
		      \+member(H,Ns)),
		P1,P2),
	minMod(kb(O,P2),KA,S2).


wfm(kb(O,P),KA,Pos,Neg,FPos,FNeg):-
	gamma(kb(O,P),KA,Neg,Pos1),
	gammaPrime(kb(O,P),KA,Pos,Neg1),
	(   (subset(Pos1,Pos),
	     subset(Neg,Neg1))->
	Pos1 = FPos,
	subtract(KA,Neg1,FNeg);
	wfm(kb(O,P),KA,Pos1,Neg1,FPos,FNeg)).

wfm(kb(O,P),Pos,Neg):-
	ka(P,KA),
	wfm(kb(O,P),KA,[],KA,Pos,Neg).

posAtom(not(L),L):-
	!.
posAtom(A,A).

removeDuplicates([],[]).
removeDuplicates([H|T],R):-
	member(H,T),
	!,
	removeDuplicates(T,R).
removeDuplicates([H|T],[H|R]):-
	removeDuplicates(T,R).

posAtoms(rule(H,B),A):-
	maplist(posAtom,[H|B],A1),
	removeDuplicates(A1,A).

ka(Rules,K):-foldl(\Rule^K1^K2^(posAtoms(Rule,A),
				union(A,K1,K2)),
		   Rules,[],K).


r(P,S,C):-
	findall(H,(
		member(rule(H,B),P), subset(B,S)),
		Hs),
	union(S,Hs,C).
d(O,S,KA,C):-
	dl_models(O,S,C1),
	include(\X^(\+(X='Thing'(_))),C1,C2),
	intersection(KA,C2,C).
t(kb(O,P),KA,S,C):-
	r(P,S,C1),
	d(O,S,KA,C2),
	union(C1,C2,C).



minM(P,I,I):-
	r(P,I,I1),
	subset(I1,I),
	!.
minM(P,I,I1):-
	r(P,I,I2),
	minM(P,I2,I1).

example(T,Pos,Neg):-
	axioms(T,O),
	rules(T,P),
	wfm(kb(O,P),Pos,Neg).
