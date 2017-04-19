:-use_module(library(apply)).
:-use_module(library(lambda)).
:-use_module(trill).

:-discontiguous rules/2.
:-discontiguous axioms/2.


rules(e1,[rule(p(a):0.6;r(a):0.4,[not(d(a)),o(a)]),
       rule(p(b):0.6;r(b):0.4,[not(d(b)),o(b)]),
       rule(e(a),[not(e(a)),o(a)]),
       rule(e(b),[not(e(b)),o(b)]),
       rule(o(b),[]),
       rule(o(a),[])]).
axioms(e1,[classAssertion(c,b),subClassOf(c,d),equivalentClasses([c,complementOf(e)]),annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',subClassOf(c,d),literal(0.2))]).


rules(e2,[rule(p(a),[not(p(a))]),
       rule(q(a),[]),
       rule(r(a),[not(r(a))])]).
axioms(e2,[subClassOf(q,complementOf(r))]).

rules(e3,[rule(exp(tts),[]),
	 rule(rec(tts),[cd(tts),not(owns(tts)),not(lowEval(tts)),int(tts)]),
	 rule(int(tts),[])]).
axioms(e3,[subClassOf(exp,complementOf(rec)),classAssertion(cd,tts)]).

rules(e4,[rule(p(X),[not(d(X)),o(X)]),
	 rule(d(X):0.7;e(X):0.3,[o(X)]),
	 rule(o(a),[]),
	 rule(o(b),[])]).
axioms(e4,[subclassOf(c,d),
	   subClassOf(intersectionOf(c,e),p),
	   annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',subClassOf(intersectionOf(c,e),p),literal(0.2))]).

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





%=============================================
create_worlds(C,L):-
	findall(W,create_single_world(C,1,W),L).

create_single_world([],P,world([],[],P)).

create_single_world([r(H,B)|T],PIn,world([r(HA,B)|TR],TA,P)):-
	member((HA:Pr),H),
	P1 is PIn*Pr,
	create_single_world(T,P1,world(TR,TA,P)).
	
create_single_world([r(H)|T],PIn,world(TR,Res,P)):-!,
	member((HA:Pr),H),
	P1 is PIn*Pr,
	create_single_world(T,P1,world(TR,TA,P)),
	(HA = '' -> Res = TA ; Res = [HA|TA]).
	
	
	

%=============================================
s(File,Worlds) :-
	atom_concat(File,'.cpl',FilePl),
	open(FilePl,read,S),
	read_clauses(S,C),
	close(S),
	(wfm_setting(universe,true) ->
		(atom_concat(File,'.uni',FileUni),
		 (exists_file(FileUni) ->
			consult(FileUni)
		  ;
		  	true
		 )
		)
	  ;
	  	true
	),
	process_clauses(C,ClausesVar),
	instantiate(ClausesVar,[],Clauses),!,
	create_worlds(Clauses,Worlds).
	/* qua si può richiamare 
	   create_single_world(Clauses,1,World)
	   che restituisce un solo mondo, quindi puoi
	   attaccare wfm su questo singolo mondo
	*/

/* predicates for producing the ground instances of program clauses */

/* instantiate(Clauses,C0,C)
	returns in C the set of clauses obtained by grounding Clauses
*/
instantiate([],C,C).

%instantiate([r(_V,[H:1],B)|T],CIn,COut):-!,
%	append(CIn,[r([H:1],B)],C1),
%	instantiate(T,C1,COut).

instantiate([r(V,H,B)|T],CIn,COut):-
	(wfm_setting(grounding,variables)->
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
	wfm_setting(ground_body,false),!.

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
	(wfm_setting(ground_body,true)->
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
	process_head(HL1,0,HL,_HLPList),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([((H:-B),V)|T],ProbAnnotAx,[r(V,HL,B)|T1]):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,_HLPList),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([((H:-B),V)|T],ProbAnnotAx,[r(V,[H:1],B)|T1]):-!,
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL,true)|T1]):-
	H=(_;_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,_HLPList),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL,true)|T1]):-
	H=(_:_),!,
	list2or(HL1,H),
	process_head(HL1,0,HL,_HLPList),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,HL)|T1]):-
	H=..[P|_Args],
	owl2_model:is_axiom(P),!,
	process_axiom(H,ProbAnnotAx,HL),
	process_clauses(T,ProbAnnotAx,T1).

process_clauses([(H,V)|T],ProbAnnotAx,[r(V,[H:1],true)|T1]):-
	process_clauses(T,ProbAnnotAx,T1).

remove_prob_annot_ax([],[],[]).

remove_prob_annot_ax([(annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(Prob)),[])|T],[(Ax,Prob)|T1],T2):- !,
	remove_prob_annot_ax(T,T1,T2).

remove_prob_annot_ax([H|T],T1,[H|T2]):-
	remove_prob_annot_ax(T,T1,T2).

process_head([H:PH],P,[H:PH1|Null],[Pred/Arity]):-
	PH1 is PH,
	PNull is 1-P-PH1,
	wfm_setting(epsilon,Eps),
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
	(wfm_setting(ground_body,true)->
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


:-dynamic wfm_setting/2.

wfm_setting(epsilon,0.00001).
wfm_setting(ground_body,true).
/* available values: true, false
if true, both the head and the body of each clause will be grounded, otherwise
only the head is grounded. In the case in which the body contains variables
not appearing in the head, the body represents an existential event */

wfm_setting(universe,true).
/* available values: true, false
if true, universe file is used
*/

wfm_setting(grounding,variables).
/* available values: variables, modes
if set to variables, the universe facts from the .uni file are used
if set to modes, the mode and type declaration from the .uni file are used
*/
