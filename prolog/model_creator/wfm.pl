:-use_module(library(apply)).
:-use_module(library(lambda)).
:-use_module(trill).

rules(e1,[rule(p(a):0.6;r(a):0.4,[not(d(a)),o(a)]),
       rule(p(b):0.6;r(b):0.4,[not(d(b)),o(b)]),
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

bodyReduct([],_,[]).
bodyReduct([not(A)|_],S,_):-
	member(A,S),
	!,
	fail.
bodyReduct([not(_)|T],S,B):-
	!,
	bodyReduct(T,S,B).
bodyReduct([H|T],S,[H|B]):-
	bodyReduct(T,S,B).

minMod(kb(O,P),KA,M):-
	minMod(kb(O,P),KA,[],M).
minMod(KB,KA,S,M):-
	t(KB,KA,S,M1),(
	subset(M1,S)->
	    S=M;
	    minMod(KB,KA,M1,M)).

kbReduct(kb(O,P),S,kb(O,P1)):-
		findall(rule(Head,Body1),
		(   member(rule(Head,Body),P),
		    bodyReduct(Body,S,Body1)
		),
		P1).

kbReduct2(kb(O,P),S,kb(O,P2)):-
	kbReduct(kb(O,P),S,kb(O,P1)),
	dl_models(O,S,A),
	findall(N,member(neg(N),A),Ns),
	include(\Rule^(Rule=rule(H,_),
		      \+member(H,Ns)),
		P1,P2).

gamma(kb(O,P),KA,S,S2):-
	kbReduct(kb(O,P),S,kb(O,P1)),
	minMod(kb(O,P1),KA,S2).
gammaPrime(kb(O,P),KA,S,S2):-
	kbReduct2(kb(O,P),S,kb(O,P2)),
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

ka(kb(_,Rules),KA):-foldl(\Rule^K1^K2^(posAtoms(Rule,A),
				union(A,K1,K2)),
		   Rules,[],KA).


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

kb(Ident,kb(O,P)):-
	axioms(Ident,O),
	rules(Ident,P).

test_ka(Ident,KA):-
	kb(Ident,KB),
	ka(KB,KA).

testReductKA(Ident,R):-
	kb(Ident,KB),
	ka(KB,KA),
	kbReduct(KB,KA,R).


testReductEmpty(Ident,R):-
	kb(Ident,KB),
	kbReduct2(KB,[],R).
	

create_worlds(P,L):-
	man_rule(P,R),
	axioms(P,A),
	append(R,A,C),
	create_world_int(C,L).

man_rule(P,R):-
	rules(P,L),
	man_rule_int(L,R).

man_rule_int([],[]).
man_rule_int([rule(H,B)|T1],[rule(HL,B)|T2]):-
	H=(_;_),!,
	list2or(HL,H),
	man_rule_int(T1,T2).
man_rule_int([rule(H,B)|T1],[rule(H1,B)|T2]):-
	is_list(H),!,
	H=[HX],
	(HX=(_:_)->H1=HX;H1=(HX:1)),
	man_rule_int(T1,T2).
man_rule_int([rule(H,B)|T1],[rule([H1],B)|T2]):-
    (H=(_:_)->H1=H;H1=(H:1)),
	man_rule_int(T1,T2).

list2or([X],X):-
		X\=;(_,_),!.

list2or([H|T],(H ; Ta)):-!,
		list2or(T,Ta).

create_world_int(C,L):-
	findall(W,create_single_world(C,1,W),L).

create_single_world([],P,world([],[],P)).

create_single_world([rule(H,B)|T],PIn,world([rule(HA,B)|TR],TA,P)):-
	is_list(H),!,
	member((HA:Pr),H),
	P1 is PIn*Pr,
	create_single_world(T,P1,world(TR,TA,P)).
create_single_world([rule(H,B)|T],PIn,world([rule(H,B)|TR],TA,P)):-!,
	create_single_world(T,PIn,world(TR,TA,P)).
create_single_world([A|T],PIn,world(TR,[A|TA],P)):-
	A\=rule(_,_),
	member(annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',A,literal(Pr)),T),!,
	P1 is PIn*Pr,
	create_single_world(T,P1,world(TR,TA,P)).
create_single_world([A|T],PIn,world(TR,[A|TA],P)):-
	A\=rule(_,_),
	create_single_world(T,PIn,world(TR,TA,P)).
create_single_world([annotationAssertion(_,_,_)|T],PIn,world(TR,TA,P)):-
	create_single_world(T,PIn,world(TR,TA,P)).
