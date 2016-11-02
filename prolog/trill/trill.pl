
:- module(trill,[sub_class/2, sub_class/3, prob_sub_class/3,
                 instanceOf/2, instanceOf/3, prob_instanceOf/3,
                 property_value/3, property_value/4, prob_property_value/4,
                 unsat/1, unsat/2, prob_unsat/2,
                 inconsistent_theory/0, inconsistent_theory/1, prob_inconsistent_theory/1,
                 axiom/1, add_kb_prefix/2, add_axiom/1, add_axioms/1, remove_kb_prefix/2, remove_kb_prefix/1, remove_axiom/1, remove_axioms/1,
                 load_kb/1, load_owl_kb/1, build_and_expand/1, instanceOf_meta/3,property_value_meta/4] ).

%:- set_prolog_flag(unknow,fail).

/*:- use_module(library('thea2/owl2_io')).
:- use_module(library('thea2/owl2_model')).*/
:- use_module(library(lists)).
:- use_module(library(ugraphs)).
:- use_module(library(rbtrees)).
:- use_module(library(dif)).
:- use_module(library(pengines)).
:- use_module(library(sandbox)).



%:- use_foreign_library(foreign(bddem),install).

:- style_check(-discontiguous).

:- multifile
	owl2_model:axiom/1,
	owl2_model:class/1,
	owl2_model:annotationProperty/1,
	owl2_model:namedIndividual/1,
	owl2_model:objectProperty/1,
	owl2_model:dataProperty/1,
	owl2_model:transitiveProperty/1,
        owl2_model:classAssertion/2,
        owl2_model:propertyAssertion/3,
        owl2_model:subPropertyOf/2,
        owl2_model:subClassOf/2,
        owl2_model:equivalentClasses/1,
        owl2_model:differentIndividuals/1,
        owl2_model:sameIndividual/1,
        owl2_model:intersectionOf/1,
        owl2_model:unionOf/1,
        owl2_model:propertyRange/2,
        owl2_model:propertyDomain/2,
        owl2_model:annotationAssertion/3,
        owl2_model:exactCardinality/2,
        owl2_model:exactCardinality/3,
        owl2_model:maxCardinality/2,
        owl2_model:maxCardinality/3,
        owl2_model:minCardinality/2,
        owl2_model:minCardinality/3,
        %lp versions
        owl2_model:lpClassAssertion/1,
        owl2_model:lpClassAssertion/2,
	owl2_model:lpPropertyAssertion/1,
        owl2_model:lpPropertyAssertion/2.


:- thread_local
	ind/1,
	exp_found/2.

/********************************
  LOAD KNOWLEDGE BASE
*********************************/
% consults a pl file and loads the contained axioms
load_kb(Name):-
  user:consult(Name).

% loads a OWL/RDF file
load_owl_kb(Name):-
  load_owl(Name).

/*****************************/

/*****************************
  UTILITY PREDICATES
******************************/
%defined in translate_rdf
:- multifile add_kb_prefix/2, add_axiom/1, add_axioms/1,
             remove_kb_prefix/2, remove_kb_prefix/1, remove_axiom/1, remove_axioms/1.

axiom(A):-
  get_trill_current_module(Name),
  Name:axiom(A).

build_and_expand(T):-
  retractall(ind(_)),
  retractall(exp_found(_,_)),
  retractall(abox(_)),
  build_abox(T),
  assert(abox([T])),
  assert(ind(1)).

instanceOf_meta(C,I,E):-
  retractall(exp_found(_,_)),
  abox(LABox),
  member((ABox,Tabs),LABox),
  %abox((ABox,Tabs)),
  add(ABox,(classAssertion(complementOf(C),I),[]),ABox0),
  %findall((ABox1,Tabs1),apply_rules_0((ABox0,Tabs),(ABox1,Tabs1)),L),
  findall((ABox1,Tabs1),apply_all_rules((ABox0,Tabs),(ABox1,Tabs1)),L),
  find_expls(L,[C,I],E),
  delete_from(L,(classAssertion(complementOf(C),I),[]),L0),
  retractall(abox(_)),
  assert(abox(L0)),
  dif(E,[]).

property_value_meta(R,I1,I2,E):-
  retractall(exp_found(_,_)),
  abox(LABox),
  member((ABox,Tabs),LABox),
  %abox((ABox,Tabs)),
  findall((ABox1,Tabs1),apply_all_rules((ABox,Tabs),(ABox1,Tabs1)),L),
  find_expls(L,[R,I1,I2],E),
  retractall(abox(_)),
  assert(abox(L)),
  dif(E,[]).

delete_from([],_,[]).

delete_from([(ABox0,Tab)|T],Q,[(ABox,Tab)|T1]):-
  %writel(ABox0),
  delete(ABox0,Q,ABox),
  delete_from(T,Q,T1).


/*****************************
  MESSAGES
******************************/
:- multifile prolog:message/1.

prolog:message(iri_not_exists) -->
  [ 'IRIs not existent' ].

prolog:message(inconsistent) -->
  [ 'Inconsistent ABox' ].

/****************************
  QUERY PREDICATES
*****************************/

/***********
  Queries
  - with and without explanations -
 ***********/
sub_class(Class,SupClass,Expl):-
  ( check_query_args([Class,SupClass],[ClassEx,SupClassEx]) *->
	unsat_internal(intersectionOf([ClassEx,complementOf(SupClassEx)]),Expl)
    ;
    	Expl = ["IRIs not existent"],!
  ).
  %subClassOf(Class,SupClass).

sub_class(Class,SupClass):-
  ( check_query_args([Class,SupClass],[ClassEx,SupClassEx]) *->
        unsat_internal(intersectionOf([ClassEx,complementOf(SupClassEx)])),!
    ;
        print_message(warning,iri_not_exists),!
  ).

instanceOf(Class,Ind,Expl):-
  ( check_query_args([Class,Ind],[ClassEx,IndEx]) *->
	retractall(exp_found(_,_)),
	retractall(ind(_)),
  	assert(ind(1)),
  	build_abox((ABox,Tabs)),
  	(  \+ clash((ABox,Tabs),_) *->
  	    (
  	    	add(ABox,(classAssertion(complementOf(ClassEx),IndEx),[]),ABox0),
	  	%findall((ABox1,Tabs1),apply_rules_0((ABox0,Tabs),(ABox1,Tabs1)),L),
  		findall((ABox1,Tabs1),apply_all_rules((ABox0,Tabs),(ABox1,Tabs1)),L),
  		find_expls(L,[ClassEx,IndEx],Expl),
  		dif(Expl,[])
  	    )
  	 ;
  	    Expl = ['Inconsistent ABox']
  	)
    ;
    	Expl = ["IRIs not existent"],!
  ).

instanceOf(Class,Ind):-
  (  check_query_args([Class,Ind],[ClassEx,IndEx]) *->
	(
	  retractall(exp_found(_,_)),
	  retractall(ind(_)),
	  assert(ind(1)),
	  build_abox((ABox,Tabs)),
	  (  \+ clash((ABox,Tabs),_) *->
	      (
	        add(ABox,(classAssertion(complementOf(ClassEx),IndEx),[]),ABox0),
	        %findall((ABox1,Tabs1),apply_rules_0((ABox0,Tabs),(ABox1,Tabs1)),L),
	  	apply_all_rules((ABox0,Tabs),(ABox1,Tabs1)),!,
	  	clash((ABox1,Tabs1),_),!
	      )
	    ;
	      print_message(warning,inconsistent)
	  )
	)
    ;
        print_message(warning,iri_not_exists),!
  ).

property_value(Prop, Ind1, Ind2,Expl):-
  ( check_query_args([Prop,Ind1,Ind2],[PropEx,Ind1Ex,Ind2Ex]) *->
	retractall(exp_found(_,_)),
	retractall(ind(_)),
  	assert(ind(1)),
  	build_abox((ABox,Tabs)),
  	(  \+ clash((ABox,Tabs),_) *->
  	    (
  	    	findall((ABox1,Tabs1),apply_all_rules((ABox,Tabs),(ABox1,Tabs1)),L),
  		find_expls(L,[PropEx,Ind1Ex,Ind2Ex],Expl),
  		dif(Expl,[])
  	    )
  	 ;
  	    Expl = ['Inconsistent ABox']
  	)
    ;
    	Expl = ["IRIs not existent"],!
  ).

property_value(Prop, Ind1, Ind2):-
  (  check_query_args([Prop,Ind1,Ind2],[PropEx,Ind1Ex,Ind2Ex]) *->
	(
	  retractall(exp_found(_,_)),
	  retractall(ind(_)),
	  assert(ind(1)),
	  build_abox((ABox,Tabs)),
	  (  \+ clash((ABox,Tabs),_) *->
	      (
	        apply_all_rules((ABox,Tabs),(ABox1,_Tabs1)),!,
	  	find((propertyAssertion(PropEx,Ind1Ex,Ind2Ex),_),ABox1),!
	      )
	    ;
	      print_message(warning,inconsistent)
	  )
	)
    ;
        print_message(warning,iri_not_exists),!
  ).


unsat(Concept,Expl):-
  (check_query_args([Concept],[ConceptEx]) *->
  	unsat_internal(ConceptEx,Expl)
    ;
    	Expl = ["IRIs not existent"]
   ).

% ----------- %
unsat_internal(Concept,Expl):-
  retractall(exp_found(_,_)),
  retractall(ind(_)),
  assert(ind(2)),
  build_abox((ABox,Tabs)),
  ( \+ clash((ABox,Tabs),_) *->
     (
     	add(ABox,(classAssertion(Concept,1),[]),ABox0),
	%findall((ABox1,Tabs1),apply_rules_0((ABox0,Tabs),(ABox1,Tabs1)),L),
	findall((ABox1,Tabs1),apply_all_rules((ABox0,Tabs),(ABox1,Tabs1)),L),
	find_expls(L,['unsat',Concept],Expl),
	dif(Expl,[])
     )
    ;
     Expl = ['Inconsistent ABox']
  ).
% ----------- %

unsat(Concept):-
  (check_query_args([Concept],[ConceptEx]) *->
  	unsat_internal(ConceptEx)
    ;
    	print_message(warning,iri_not_exists)
   ).

% ----------- %
unsat_internal(Concept):-
  retractall(exp_found(_,_)),
  retractall(ind(_)),
  assert(ind(2)),
  build_abox((ABox,Tabs)),
  ( \+ clash((ABox,Tabs),_) *->
     (
     	add(ABox,(classAssertion(Concept,1),[]),ABox0),
  	%findall((ABox1,Tabs1),apply_rules_0((ABox0,Tabs),(ABox1,Tabs1)),L),
  	apply_all_rules((ABox0,Tabs),(ABox1,Tabs1)),!,
  	clash((ABox1,Tabs1),_),!
     )
    ;
     print_message(warning,inconsistent)
  ).
% ----------- %

inconsistent_theory(Expl):-
  retractall(exp_found(_,_)),
  retractall(ind(_)),
  assert(ind(1)),
  build_abox((ABox,Tabs)),
  findall((ABox1,Tabs1),apply_all_rules((ABox,Tabs),(ABox1,Tabs1)),L),
  find_expls(L,['inconsistent','kb'],Expl),
  dif(Expl,[]).

inconsistent_theory:-
  retractall(exp_found(_,_)),
  retractall(ind(_)),
  assert(ind(1)),
  build_abox((ABox,Tabs)),
  \+ clash((ABox,Tabs),_),!,
  apply_all_rules((ABox,Tabs),(ABox1,Tabs1)),!,
  clash((ABox1,Tabs1),_),!.

inconsistent_theory:-
  print_message(warning,inconsistent).

prob_instanceOf(Class,Ind,P):-
  ( check_query_args([Class,Ind],[ClassEx,IndEx]) *->
  	all_instanceOf(ClassEx,IndEx,Exps),
%  (Exps \= [] *->
%    build_formula(Exps,FormulaE,[],VarE),
%    (FormulaE \= [] *->
%      var2numbers(VarE,0,NewVarE),
%      write(NewVarE),nl,write(FormulaE),
%      compute_prob(NewVarE,FormulaE,P,0)
%    ;
%      P = 1)
%  ;
%    P = 0).
%  writel(Exps),nl,
  	compute_prob(Exps,P)
  ;
  	P = ["IRIs not existent"],!
  ).

prob_property_value(Prop, Ind1, Ind2,P):-
  ( check_query_args([Prop,Ind1,Ind2],[PropEx,Ind1Ex,Ind2Ex]) *->
  	all_property_value(PropEx,Ind1Ex,Ind2Ex,Exps),
%  (Exps \= [] *->
%    build_formula(Exps,FormulaE,[],VarE),
%    (FormulaE \= [] *->
%      var2numbers(VarE,0,NewVarE),
%      write(NewVarE),nl,write(FormulaE),
%      compute_prob(NewVarE,FormulaE,P,0)
%    ;
%      P = 1)
%  ;
%    P = 0).
%  writel(Exps),nl,
  	compute_prob(Exps,P)
  ;
  	P = ["IRIs not existent"],!
  ).

prob_sub_class(Class,SupClass,P):-
  ( check_query_args([Class,SupClass],[ClassEx,SupClassEx]) *->
  	all_sub_class(ClassEx,SupClassEx,Exps),
%  (Exps \= [] *->
%    build_formula(Exps,FormulaE,[],VarE),
%    (FormulaE \= [] *->
%      var2numbers(VarE,0,NewVarE),
%      compute_prob(NewVarE,FormulaE,P,0)
%    ;
%      P = 1)
%  ;
%    P = 0).
  	compute_prob(Exps,P)
  ;
  	P = ["IRIs not existent"],!
  ).

prob_unsat(Concept,P):-
  check_query_args([Concept],[ConceptEx]),
  all_unsat(ConceptEx,Exps),
  compute_prob(Exps,P).

prob_inconsistent_theory(P):-
  all_inconsistent_theory(Exps),
  compute_prob(Exps,P).

/***********
  Utilities for queries
 ***********/

% to find all axplanations for probabilistic queries
all_sub_class(Class,SupClass,LE):-
  all_unsat(intersectionOf([Class,complementOf(SupClass)]),LE).

all_instanceOf(Class,Ind,LE):-
  findall(Expl,instanceOf(Class,Ind,Expl),LE).

all_property_value(Prop,Ind1,Ind2,LE):-
  findall(Expl,property_value(Prop,Ind1,Ind2,Expl),LE).

all_unsat(Concept,LE):-
  findall(Expl,unsat_internal(Concept,Expl),LE).


all_inconsistent_theory(LE):-
  findall(Expl,inconsistent_theory(Expl),LE).



% expands query arguments using prefixes and checks their existence in the kb
check_query_args(L,LEx) :-
  get_trill_current_module(Name),
  Name:ns4query(NSList),
  expand_all_ns(L,NSList,LEx), %from translate_rdf module
  check_query_args_presence(LEx,Name).

check_query_args_presence([],_).

check_query_args_presence([H|T],Name) :-
  atomic(H),!,
  find_atom_in_axioms(Name,H),%!,
  check_query_args_presence(T,Name).

check_query_args_presence([H|T],Name) :-
  \+ atomic(H),!,
  H =.. [_|L],
  flatten(L,L1),
  check_query_args_presence(L1,Name),
  check_query_args_presence(T,Name).

% looks for presence of atoms in kb's axioms
find_atom_in_axioms(Name,H):-
  Name:axiom(A),
  A =.. [_|L],
  flatten(L,L1),
  member(H,L1),!.

find_atom_in_axioms(Name,H):-
  (
    (
      ( Name:class(A) ; Name:annotationProperty(A) ; Name:namedIndividual(A) ; Name:objectProperty(A) ;
        Name:dataProperty(A)
      ),
      L=[A]
    )
   ;(
      ( Name:classAssertion(A,B) ; Name:subPropertyOf(A,B) ; Name:subClassOf(A,B) ; Name:propertyRange(A,B) ;
        Name:propertyDomain(A,B) ; Name:exactCardinality(A,B) ; Name:maxCardinality(A,B) ; Name:minCardinality(A,B)
      ),
      L=[A,B]
    )
   ;
    (
      ( Name:propertyAssertion(A,B,C) ; Name:annotationAssertion(A,B,C) ; Name:exactCardinality(A,B,C) ;
        Name:maxCardinality(A,B,C) ; Name:minCardinality(A,B,C)
      ),
      L=[A,B,C]
    )
   ;
    Name:equivalentClasses(L)
   ;
    Name:differentIndividuals(L)
   ;
    Name:sameIndividual(L)
   ;
    Name:intersectionOf(L)
   ;
    Name:unionOf(L)
  ),
  flatten(L,L1),
  member(H,L1),!.

% checks if an explanations was already found
find_expls(ABoxes,E):-
  find_expls(ABoxes,['standard','query'],E).

find_expls([],[_,_],[]).

find_expls([ABox|_T],[C,I],E):-
  clash(ABox,E0),
  \+ member(lpClassAssertion(C,I),E0),
  sort(E0,E),
  (
    (member(Ax,E),
     Ax\=lpClassAssertion(_,_),
     Ax\=lpPropertyAssertion(_,_,_)) ->
  	(findall(Exp,exp_found([C,I],Exp),Expl),
  	 not_already_found(Expl,[C,I],E),
  	 assert(exp_found([C,I],E))
  	)
    ;
	false
  ).

find_expls([_ABox|T],[C,I],Expl):-
  \+ length(T,0),
  find_expls(T,[C,I],Expl).

% checks if an explanations was already found (property_value version)
find_expls([],[_,_,_],[]).

find_expls([(ABox,_)|_T],[PropEx,Ind1Ex,Ind2Ex],E):-
  find((propertyAssertion(PropEx,Ind1Ex,Ind2Ex),E),ABox),
  \+ member(lpPropertyAssertion(PropEx,Ind1Ex,Ind2Ex),E),
  (
    (member(Ax,E),
     Ax\=lpClassAssertion(_,_),
     Ax\=lpPropertyAssertion(_,_,_)) ->
  	(findall(Exp,exp_found([PropEx,Ind1Ex,Ind2Ex],Exp),Expl),
  	 not_already_found(Expl,[PropEx,Ind1Ex,Ind2Ex],E),
  	 assert(exp_found([PropEx,Ind1Ex,Ind2Ex],E))
  	)
    ;
	false
  ).

find_expls([_ABox|T],[PropEx,Ind1Ex,Ind2Ex],Expl):-
  \+ length(T,0),
  find_expls(T,[PropEx,Ind1Ex,Ind2Ex],Expl).

not_already_found([],_Q,_E):-!.

not_already_found([H|_T],_Q,E):-
  subset(H,E),!,
  fail.

not_already_found([H|_T],Q,E):-
  subset(E,H),!,
  retract(exp_found(Q,H)).

not_already_found([_H|T],Q,E):-
  not_already_found(T,Q,E).

/****************************/

/**************
  FIND FUNCTIONS
***************/

findClassAssertion(C,Ind,Expl1,ABox):-
	find((classAssertion(C,Ind),Expl1),ABox).
findClassAssertion(C,Ind,[lpClassAssertion(C,Ind)],ABox):-
	(   ground(Ind) -> true;
	find((classAssertion(_,Ind),_),ABox)),
	owl2_model:lpClassAssertion(C).

findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox):-
	find((propertyAssertion(R,Ind1,Ind2),Expl1),ABox).
findPropertyAssertion(R,Ind1,Ind2,[lpPropertyAssertion(R,Ind1,Ind2)],ABox):-
	(   (ground(Ind1),ground(Ind2)) -> true;
	find((propertyAssertion(_,Ind1,Ind2),_),ABox)),
	owl2_model:lpPropertyAssertion(R).


/****************************
  TABLEAU ALGORITHM
****************************/

/*
find_clash((ABox0,Tabs0),Expl2):-
  apply_rules((ABox0,Tabs0),(ABox,Tabs)),
  clash((ABox,Tabs),Expl).
*/

%-------------
% clash managing
% previous version, manages only one clash at time
% need some tricks in some rules for managing the cases of more than one clash
% TO IMPROVE!
%------------
clash((ABox,_),Expl):-
  %write('clash 1'),nl,
  findClassAssertion(C,Ind,Expl1,ABox),
  findClassAssertion(complementOf(C),Ind,Expl2,ABox),
  append(Expl1,Expl2,Expl).

clash((ABox,_),Expl):-
  %write('clash 2'),nl,
  find((sameIndividual(LS),Expl1),ABox),
  find((differentIndividuals(LD),Expl2),ABox),
  member(X,LS),
  member(Y,LS),
  member(X,LD),
  member(Y,LD),
  dif(X,Y),
  append(Expl1,Expl2,Expl).

clash((ABox,_),Expl):-
  %write('clash 3'),nl,
  findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
  findClassAssertion(complementOf(C),sameIndividual(L2),Expl2,ABox),
  member(X,L1),
  member(X,L2),!,
  append(Expl1,Expl2,Expl).

clash((ABox,_),Expl):-
  %write('clash 4'),nl,
  findClassAssertion(C,Ind1,Expl1,ABox),
  findClassAssertion(complementOf(C),sameIndividual(L2),Expl2,ABox),
  member(Ind1,L2),
  append(Expl1,Expl2,Expl).

clash((ABox,_),Expl):-
  %write('clash 5'),nl,
  findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
  findClassAssertion(complementOf(C),Ind2,Expl2,ABox),
  member(Ind2,L1),
  append(Expl1,Expl2,Expl).

clash((ABox,Tabs),Expl):-
  %write('clash 6'),nl,
  findClassAssertion(maxCardinality(N,S,C),Ind,Expl1,ABox),
  s_neighbours(Ind,S,(ABox,Tabs),SN),
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  make_expl(Ind,S,SNC,Expl1,ABox,Expl2),
  flatten(Expl2,Expl3),
  list_to_set(Expl3,Expl).

clash((ABox,Tabs),Expl):-
  %write('clash 7'),nl,
  findClassAssertion(maxCardinality(N,S),Ind,Expl1,ABox),
  s_neighbours(Ind,S,(ABox,Tabs),SN),
  length(SN,LSS),
  LSS @> N,
  make_expl(Ind,S,SN,Expl1,ABox,Expl2),
  flatten(Expl2,Expl3),
  list_to_set(Expl3,Expl).

% --------------
make_expl(_,_,[],Expl1,_,Expl1).

make_expl(Ind,S,[H|T],Expl1,ABox,[Expl2|Expl]):-
  findPropertyAssertion(S,Ind,H,Expl2,ABox),
  make_expl(Ind,S,T,Expl1,ABox,Expl).


% -------------
% rules application
% -------------
apply_all_rules(ABox0,ABox):-
  apply_det_rules([o_rule,and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule,min_rule],ABox0,ABox1),
  (ABox0=ABox1 *->
  ABox=ABox1;
  apply_all_rules(ABox1,ABox)).

apply_det_rules([],ABox0,ABox):-
  apply_nondet_rules([or_rule,max_rule],ABox0,ABox).

apply_det_rules([H|_],ABox0,ABox):-
  %C=..[H,ABox,ABox1],
  call(H,ABox0,ABox),!.

apply_det_rules([_|T],ABox0,ABox):-
  apply_det_rules(T,ABox0,ABox).


apply_nondet_rules([],ABox,ABox).

apply_nondet_rules([H|_],ABox0,ABox):-
  %C=..[H,ABox,L],
  call(H,ABox0,L),!,
  member(ABox,L),
  dif(ABox0,ABox).

apply_nondet_rules([_|T],ABox0,ABox):-
  apply_nondet_rules(T,ABox0,ABox).


/*
apply_all_rules(ABox0,ABox):-
  apply_nondet_rules([or_rule,max_rule],
                  ABox0,ABox1),
  (ABox0=ABox1 *->
  ABox=ABox1;
  apply_all_rules(ABox1,ABox)).

apply_det_rules([],ABox,ABox).
apply_det_rules([H|_],ABox0,ABox):-
  %C=..[H,ABox,ABox1],
  once(call(H,ABox0,ABox)).
apply_det_rules([_|T],ABox0,ABox):-
  apply_det_rules(T,ABox0,ABox).
apply_nondet_rules([],ABox0,ABox):-
  apply_det_rules([o_rule,and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule,min_rule],ABox0,ABox).
apply_nondet_rules([H|_],ABox0,ABox):-
  %C=..[H,ABox,L],
  once(call(H,ABox0,L)),
  member(ABox,L),
  dif(ABox0,ABox).
apply_nondet_rules([_|T],ABox0,ABox):-
  apply_nondet_rules(T,ABox0,ABox).
*/

/**********************
   old version for the rules application

apply_rules_0((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules((ABox0,Tabs0),(ABox,Tabs)).

apply_rules((ABox0,Tabs0),(ABox,Tabs)):-
  %writel(ABox0),nl,
  %apply_rules1((ABox0,Tabs0),(ABox,Tabs)).
  apply_rules1_1((ABox0,Tabs0),(ABox,Tabs)).

apply_rules1_1((ABox0,Tabs0),(ABox,Tabs)):-
  %write('o_rule: '),nl,
  o_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules1_1((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules1((ABox0,Tabs0),(ABox,Tabs)).

apply_rules1((ABox0,Tabs0),(ABox,Tabs)):-
  %write('and_rule: '),nl,
  and_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules1((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules2((ABox0,Tabs0),(ABox,Tabs)).

apply_rules2((ABox0,Tabs0),(ABox,Tabs)):-
  %write('exists_rule: '),nl,
  exists_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules2((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules3((ABox0,Tabs0),(ABox,Tabs)).

apply_rules3((ABox0,Tabs0),(ABox,Tabs)):-
  %write('forall_rule: '), nl,
  forall_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules3((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules3_1((ABox0,Tabs0),(ABox,Tabs)).

apply_rules3_1((ABox0,Tabs0),(ABox,Tabs)):-
  %write('forall_plus_rule: '),nl,
  forall_plus_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules3_1((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules4((ABox0,Tabs0),(ABox,Tabs)).

apply_rules4((ABox0,Tabs0),(ABox,Tabs)):-
  %write('min_rule: '),nl,
  min_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules4((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules5((ABox0,Tabs0),(ABox,Tabs)).

apply_rules5((ABox0,Tabs0),(ABox,Tabs)):-
  %write('unfold_rule: '),nl,
  unfold_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules5((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules6((ABox0,Tabs0),(ABox,Tabs)).

apply_rules6((ABox0,Tabs0),(ABox,Tabs)):-
  %write('add_exists_rule: '),nl,
  add_exists_rule((ABox0,Tabs0),(ABox1,Tabs1)),!,
  %writel(ABox1),nl,
  %write('apllyied'),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules6((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules7((ABox0,Tabs0),(ABox,Tabs)).

apply_rules7((ABox0,Tabs0),(ABox,Tabs)):-
  %write('or_rule: '),nl,
  or_rule((ABox0,Tabs0),L),!,
  member((ABox1,Tabs1),L),
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules7((ABox0,Tabs0),(ABox,Tabs)):-
  apply_rules8((ABox0,Tabs0),(ABox,Tabs)).

apply_rules8((ABox0,Tabs0),(ABox,Tabs)):-
  %write('max_rule: '),nl,
  max_rule((ABox0,Tabs0),L),!,
  member((ABox1,Tabs1),L),
  %write('apllyied'),nl,
  %writel(ABox1),nl,
  apply_rules((ABox1,Tabs1),(ABox,Tabs)).

apply_rules8((ABox,Tabs),(ABox,Tabs)).

*/


/***********
  rules
************/
/*
  add_exists_rule
  ========================
*/
add_exists_rule((ABox,Tabs),([(classAssertion(someValuesFrom(R,C),Ind1),Expl)|ABox],Tabs)):-
  findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox),
  findClassAssertion(C,Ind2,Expl2,ABox),
  existsInKB(R,C),
  append(Expl1,Expl2,ExplT),
  list_to_set(ExplT,Expl),
  absent(classAssertion(someValuesFrom(R,C),Ind1),Expl,(ABox,Tabs)).

existsInKB(R,C):-
  get_trill_current_module(Name),
  Name:subClassOf(A,B),
  member(someValuesFrom(R,C),[A,B]).

existsInKB(R,C):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(someValuesFrom(R,C),L).

/* *************** */ 

/*
  and_rule
  =================
*/
and_rule((ABox0,Tabs0),(ABox,Tabs0)):-
  findClassAssertion(intersectionOf(LC),Ind,Expl,ABox0),
  \+ indirectly_blocked(Ind,(ABox0,Tabs0)),
  scan_and_list(LC,Ind,Expl,ABox0,Tabs0,ABox,0).


%----------------
scan_and_list([],_Ind,_Expl,ABox,_Tabs,ABox,Mod):-
  dif(Mod,0).

scan_and_list([C|T],Ind,Expl,ABox0, Tabs0,[(classAssertion(C,Ind),Expl)|ABox],_Mod):-
  absent(classAssertion(C,Ind),Expl,(ABox0,Tabs0)),!,
  scan_and_list(T,Ind,Expl,ABox0, Tabs0, ABox,1).

scan_and_list([_C|T],Ind,Expl,ABox0,Tabs0,ABox,Mod):-
  scan_and_list(T,Ind,Expl,ABox0, Tabs0, ABox,Mod).
/* ************* */

/*
  or_rule
  ===============
*/
or_rule((ABox0,Tabs0),L):-
  findClassAssertion(unionOf(LC),Ind,Expl,ABox0),
  \+ indirectly_blocked(Ind,(ABox0,Tabs0)),
  not_ind_intersected_union(Ind,LC,ABox0),
  length(LC,NClasses),
  findall((ABox1,Tabs0),scan_or_list(LC,NClasses,Ind,Expl,ABox0,Tabs0, ABox1),L),
  dif(L,[]),!.

not_ind_intersected_union(Ind,LC,ABox):-
  \+ ind_intersected_union(Ind,LC,ABox).

ind_intersected_union(Ind,LC,ABox) :-
  findClassAssertion(C,Ind,_,ABox),
  member(C,LC),!.
%---------------
scan_or_list([C],1,Ind,Expl,ABox, Tabs, [(classAssertion(C,Ind),Expl)|ABox]):-
  absent(classAssertion(C,Ind),Expl,(ABox,Tabs)),!.

scan_or_list([C|_T],_NClasses,Ind,Expl,ABox, Tabs, [(classAssertion(C,Ind),Expl)|ABox]):-
  absent(classAssertion(C,Ind),Expl,(ABox,Tabs)).

scan_or_list([_C|T],NClasses,Ind,Expl,ABox0,Tabs, ABox):-
  NC is NClasses - 1,
  scan_or_list(T,NC,Ind,Expl,ABox0, Tabs,ABox).
/* ***************+ */

/*
  exists_rule
  ==================
*/
exists_rule((ABox0,Tabs0),([(propertyAssertion(R,Ind1,Ind2),Expl),
    (classAssertion(C,Ind2),Expl)|ABox0],Tabs)):-
  findClassAssertion(someValuesFrom(R,C),Ind1,Expl,ABox0),
  \+ blocked(Ind1,(ABox0,Tabs0)),
  \+ connected_individual(R,C,Ind1,ABox0),
  new_ind(Ind2),
  add_edge(R,Ind1,Ind2,Tabs0,Tabs).


%---------------
connected_individual(R,C,Ind1,ABox):-
  findPropertyAssertion(R,Ind1,Ind2,_,ABox),
  findClassAssertion(C,Ind2,_,ABox).

/* ************ */

/*
  forall_rule
  ===================
*/
forall_rule((ABox,Tabs),([(classAssertion(C,Ind2),Expl)|ABox],Tabs)):-
  findClassAssertion(allValuesFrom(R,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,(ABox,Tabs)),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  append(Expl1,Expl2,ExplT),
  list_to_set(ExplT,Expl), %list_to_set(ExplT,ExplT1),
  %check_chain(R,Ind1,Ind2,ExplT1,ExplT1,Expl),
  absent(classAssertion(C,Ind2),Expl,(ABox,Tabs)).

%------------------
check_chain(_,_,_,[],Ne,Ne):-
  !.

check_chain(R,Ind1,Ind2,[subPropertyOf(R,S,Ind3,Ind1)|T],Ne,Ne4):-
  is_transitive(R,S,Ne),
  copy_s(subPropertyOf(R,S,Ind3,Ind1),subPropertyOf(R,S,Ind3,Ind2),Ne,Ne2),
  check_chain(R,Ind1,Ind2,T,Ne2,Ne3),!,
  check_chain(S,Ind3,Ind2,Ne3,Ne3,Ne4).

check_chain(R,Ind1,Ind2,[transitive(R,[Ind3,Ind1])|T],Ne,Ne3):-
  copy_s(transitive(R,[Ind3,Ind1]),transitive(R,[Ind3,Ind1,Ind2]),Ne,Ne2),
  check_chain(R,Ind1,Ind2,T,Ne2,Ne3),!.

check_chain(R,Ind1,Ind2,[transitive(R,[Ind3,Ind4,Ind1])|T],Ne,Ne3):-
  copy_s(transitive(R,[Ind3,Ind4,Ind1]),transitive(R,[Ind3,Ind4,Ind2]),Ne,Ne2),
  check_chain(R,Ind1,Ind2,T,Ne2,Ne3),!.

check_chain(R,Ind1,Ind2,[_H|T],Ne,Ne1):-
  check_chain(R,Ind1,Ind2,T,Ne,Ne1),!.

% ------------------
is_transitive(R,_S,Ne):-
  %member(transitive(R,_),Ne),!.
  member(transitive(R),Ne),!.

is_transitive(_R,S,Ne):-
  %member(transitive(S,_),Ne),!.
  member(transitive(S),Ne),!.
% ------------------
copy_s(_,_,[],[]).

copy_s(AxO,AxN,[AxO|T],[AxN|T1]):-
  copy_s(AxO,AxN,T,T1).

copy_s(AxO,AxN,[H|T],[H|T1]):-
  copy_s(AxO,AxN,T,T1).
/* ************** */

/*
  forall_plus_rule
  =================
*/
forall_plus_rule((ABox,Tabs),([(classAssertion(allValuesFrom(R,C),Ind2),Expl)| ABox],Tabs)):-
  findClassAssertion(allValuesFrom(S,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,(ABox,Tabs)),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  find_sub_sup_trans_role(R,S,Ind1,Ind2,Expl3),
  append(Expl1,Expl2,ExplT),
  append(ExplT,Expl3,ExplT1),
  list_to_set(ExplT1,Expl),
  absent(classAssertion(allValuesFrom(R,C),Ind2),Expl,(ABox,Tabs)).

% --------------
find_sub_sup_trans_role(R,S,_Ind1,_Ind2,[subPropertyOf(R,S),transitive(R)]):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S),
  Name:transitiveProperty(R).

find_sub_sup_trans_role(R,S,_Ind1,_Ind2,[subPropertyOf(R,S)]):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S),
  \+ Name:transitiveProperty(R).
/* ************ */

/*
  unfold_rule
  ===========
*/

unfold_rule((ABox0,Tabs),([(classAssertion(D,Ind),[Ax|Expl])|ABox],Tabs)):-
  findClassAssertion(C,Ind,Expl,ABox0),
  find_sub_sup_class(C,D,Ax),
  absent(classAssertion(D,Ind),[Ax|Expl],(ABox0,Tabs)),
  add_nominal(D,Ind,ABox0,ABox).

/* -- unfold_rule
      takes a class C1 in which Ind belongs, find a not atomic class C
      that contains C1 (C is seen as list of classes), controls if
      the individual Ind belongs to all those classes, if yes find a class D (if exists)
      that is the superclass or an equivalent class of C and adds D to label af Ind
      - for managing tableau with more than one clash -
   --
*/
unfold_rule((ABox0,Tabs),([(classAssertion(D,Ind),[Ax|Expl1])|ABox],Tabs)):-
  findClassAssertion(C1,Ind,Expl,ABox0),
  find_not_atomic(C1,C,L),
  ( C = unionOf(_) -> Expl1 = Expl ; find_all(Ind,L,ABox0,Expl1)),
  find_sub_sup_class(C,D,Ax),
  absent(classAssertion(D,Ind),[Ax|Expl1],(ABox0,Tabs)),
  add_nominal(D,Ind,ABox0,ABox).

/* -- unfold_rule
 *    control propertyRange e propertyDomain
 * --
 */
unfold_rule((ABox0,Tabs),([(classAssertion(D,Ind),Expl)|ABox],Tabs)):-
  find_class_prop_range_domain(Ind,D,Expl,(ABox0,Tabs)),
  absent(classAssertion(D,Ind),Expl,(ABox0,Tabs)),
  add_nominal(D,Ind,ABox0,ABox).

/*
 * -- unfold_rule
 *    manage the negation
 * --
 */
unfold_rule((ABox0,Tabs),([(classAssertion(D,Ind),[complementOf(C)|Expl])|ABox],Tabs)):-
  findClassAssertion(complementOf(C),Ind,Expl,ABox0),
  find_neg_class(C,D),
  absent(classAssertion(D,Ind),[complementOf(C)|Expl],(ABox0,Tabs)),
  add_nominal(D,Ind,ABox0,ABox).

% ----------------
% add_nominal

add_nominal(D,Ind,ABox0,ABox):-
  ((D = oneOf(_),
    \+ member(nominal(Ind),ABox0))
    *->
   (
     ABox1 = [nominal(Ind)|ABox0],
     (member((classAssertion('Thing',Ind),_E),ABox1)
     ->
     ABox = ABox1
     ;
     ABox = [(classAssertion('Thing',Ind),[])|ABox1]
     )
   )
    ;
   ABox = ABox0
  ).

% ----------------
% unionOf, intersectionOf, subClassOf, negation, allValuesFrom, someValuesFrom, exactCardinality(min and max), maxCardinality, minCardinality

find_neg_class(unionOf(L),intersectionOf(NL)):-
  neg_list(L,NL).

find_neg_class(intersectionOf(L),unionOf(NL)):-
  neg_list(L,NL).

find_neg_class(subClassOf(C,D),intersectionOf(C,ND)):-
  neg_class(D,ND).

find_neg_class(complementOf(C),C).

find_neg_class(allValuesFrom(R,C),someValuesFrom(R,NC)):-
  neg_class(C,NC).

find_neg_class(someValuesFrom(R,C),allValuesFrom(R,NC)):-
  neg_class(C,NC).

find_neg_class(exactCardinality(N,R,C),unionOf([maxCardinality(NMax,R,C),minCardinality(NMin,R,C)])):-
  NMax is N - 1,
  NMin is N + 1.

find_neg_class(minCardinality(N,R,C),maxCardinality(NMax,R,C)):-
  NMax is N - 1.

find_neg_class(maxCardinality(N,R,C),minCardinality(NMin,R,C)):-
  NMin is N + 1.

% ---------------

neg_class(complementOf(C),C):- !.

neg_class(C,complementOf(C)).

% ---------------

neg_list([],[]).

neg_list([H|T],[complementOf(H)|T1]):-
  neg_list(T,T1).

neg_list([complementOf(H)|T],[H|T1]):-
  neg_list(T,T1).

% ----------------

find_class_prop_range_domain(Ind,D,[propertyRange(R,D)|ExplPA],(ABox,_Tabs)):-
  findPropertyAssertion(R,_,IndL,ExplPA,ABox),
  indAsList(IndL,L),
  member(Ind,L),
  get_trill_current_module(Name),
  Name:propertyRange(R,D).

find_class_prop_range_domain(Ind,D,[propertyDomain(R,D)|ExplPA],(ABox,_Tabs)):-
  findPropertyAssertion(R,IndL,_,ExplPA,ABox),
  indAsList(IndL,L),
  member(Ind,L),
  get_trill_current_module(Name),
  Name:propertyDomain(R,D).


%-----------------
% subClassOf
find_sub_sup_class(C,D,subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%equivalentClasses
find_sub_sup_class(C,D,equivalentClasses(L)):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(C,L),
  member(D,L),
  dif(C,D).

%concept for concepts allValuesFrom
find_sub_sup_class(allValuesFrom(R,C),allValuesFrom(R,D),subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%role for concepts allValuesFrom
find_sub_sup_class(allValuesFrom(R,C),allValuesFrom(S,C),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%concept for concepts someValuesFrom
find_sub_sup_class(someValuesFrom(R,C),someValuesFrom(R,D),subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%role for concepts someValuesFrom
find_sub_sup_class(someValuesFrom(R,C),someValuesFrom(S,C),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%role for concepts exactCardinality
find_sub_sup_class(exactCardinality(N,R),exactCardinality(N,S),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%concept for concepts exactCardinality
find_sub_sup_class(exactCardinality(N,R,C),exactCardinality(N,R,D),subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%role for concepts exactCardinality
find_sub_sup_class(exactCardinality(N,R,C),exactCardinality(N,S,C),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%role for concepts maxCardinality
find_sub_sup_class(maxCardinality(N,R),maxCardinality(N,S),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%concept for concepts maxCardinality
find_sub_sup_class(maxCardinality(N,R,C),maxCardinality(N,R,D),subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%role for concepts maxCardinality
find_sub_sup_class(minCardinality(N,R,C),maxCardinality(N,S,C),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%role for concepts minCardinality
find_sub_sup_class(minCardinality(N,R),minCardinality(N,S),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

%concept for concepts minCardinality
find_sub_sup_class(minCardinality(N,R,C),minCardinality(N,R,D),subClassOf(C,D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D).

%role for concepts minCardinality
find_sub_sup_class(minCardinality(N,R,C),minCardinality(N,S,C),subPropertyOf(R,S)):-
  get_trill_current_module(Name),
  Name:subPropertyOf(R,S).

/*******************
 managing the concept (C subclassOf Thing)
 this implementation doesn't work well in a little set of cases
 TO IMPROVE!
 *******************

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:subClassOf(A,B),
  member(C,[A,B]),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:classAssertion(C,_),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(C,L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:unionOf(L),
  member(C,L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(someValuesFrom(_,C),L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(allValuesFrom(_,C),L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(minCardinality(_,_,C),L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(maxCardinality(_,_,C),L),!.

find_sub_sup_class(C,'Thing',subClassOf(C,'Thing')):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(exactCardinality(_,_,C),L),!.

*/

%--------------------
% looks for not atomic concepts descriptions containing class C
find_not_atomic(C,intersectionOf(L1),L1):-
  get_trill_current_module(Name),
  Name:subClassOf(A,B),
  member(intersectionOf(L1),[A,B]),
  member(C,L1).

find_not_atomic(C,unionOf(L1),L1):-
  get_trill_current_module(Name),
  Name:subClassOf(A,B),
  member(unionOf(L1),[A,B]),
  member(C,L1).

find_not_atomic(C,intersectionOf(L),L):-
  get_trill_current_module(Name),
  Name:intersectionOf(L),
  member(C,L).

find_not_atomic(C,unionOf(L),L):-
  get_trill_current_module(Name),
  Name:unionOf(L),
  member(C,L).

find_not_atomic(C,intersectionOf(L1),L1):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(intersectionOf(L1),L),
  member(C,L1).

find_not_atomic(C,unionOf(L1),L1):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(unionOf(L1),L),
  member(C,L1).

% -----------------------
% puts together the explanations of all the concepts found by find_not_atomic/3
find_all(_,[],_,[]).

find_all(Ind,[H|T],ABox,ExplT):-
  findClassAssertion(H,Ind,Expl1,ABox),
  find_all(Ind,T,ABox,Expl),
  append(Expl,Expl1,Expl2),
  list_to_set(Expl2,ExplT).


/* ************* */

/*
  ce_rule
  =============
*/
ce_rule((ABox0,(T,RBN,RBR)),(ABox,(T,RBN,RBR))):-
  find_not_sub_sup_class(Ax,UnAx),
  vertices(T,Inds),
  apply_ce_to(Inds,Ax,UnAx,ABox0,ABox,(T,RBN,RBR),C),
  C @> 0.


% ------------------
find_not_sub_sup_class(subClassOf(C,D),unionOf(complementOf(C),D)):-
  get_trill_current_module(Name),
  Name:subClassOf(C,D),
  \+ atomic(C).


find_not_sub_sup_class(equivalentClasses(L),unionOf(L1)):-
  get_trill_current_module(Name),
  Name:equivalentClasses(L),
  member(C,L),
  \+ atomic(C),
  copy_neg_c(C,L,L1).

%-------------------------
copy_neg_c(_,[],[]).

copy_neg_c(C,[C|T],[complementOf(C)|T1]):-
  !,
  copy_neg_c(C,T,T1).

copy_neg_c(C,[H|T],[H|T1]):-
  copy_neg_c(C,T,T1).

%---------------------
apply_ce_to([],_,_,ABox,ABox,_,0).

apply_ce_to([Ind|T],Ax,UnAx,ABox0,[(classAssertion(UnAx,Ind),[Ax])|ABox],Tabs,C):-
  \+ indirectly_blocked(Ind,(ABox0,Tabs)),
  absent(classAssertion(UnAx,Ind),[Ax],(ABox0,Tabs)),!,
  apply_ce_to(T,Ax,UnAx,ABox0,ABox,Tabs,C0),
  C is C0 + 1.

apply_ce_to([_Ind|T],Ax,UnAx,ABox0,ABox,Tabs,C):-
  apply_ce_to(T,Ax,UnAx,ABox0,ABox,Tabs,C).

/* **************** */

/*
  min_rule
  =============
*/
min_rule((ABox,Tabs),([(differentIndividuals(NI),Expl)|ABox1],Tabs1)):-
  findClassAssertion(minCardinality(N,S),Ind1,Expl,ABox),
  \+ blocked(Ind1,(ABox,Tabs)),
  s_neighbours(Ind1,S,(ABox,Tabs),SN),
  safe_s_neigh(SN,S,(ABox,Tabs),SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh(NoI,S,Ind1,Expl,NI,ABox,Tabs,ABox1,Tabs1).


min_rule((ABox,Tabs),([(differentIndividuals(NI),Expl)|ABox1],Tabs1)):-
  findClassAssertion(minCardinality(N,S,C),Ind1,Expl,ABox),
  \+ blocked(Ind1,(ABox,Tabs)),
  s_neighbours(Ind1,S,(ABox,Tabs),SN),
  safe_s_neigh(SN,S,(ABox,Tabs),SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh_C(NoI,S,C,Ind1,Expl,NI,ABox,Tabs,ABox1,Tabs1).

% ----------------------
min_rule_neigh(0,_,_,_,[],ABox,Tabs,ABox,Tabs).

min_rule_neigh(N,S,Ind1,Expl,[Ind2|NI],ABox,Tabs,[(propertyAssertion(S,Ind1,Ind2),Expl)|ABox2],Tabs2):-
  N > 0,
  NoI is N-1,
  new_ind(Ind2),
  add_edge(S,Ind1,Ind2,Tabs,Tabs1),
  check_block(Ind2,([(propertyAssertion(S,Ind1,Ind2),Expl)|ABox],Tabs)),
  min_rule_neigh(NoI,S,Ind1,Expl,NI,ABox,Tabs1,ABox2,Tabs2).

%----------------------
min_rule_neigh_C(0,_,_,_,_,[],ABox,Tabs,ABox,Tabs).

min_rule_neigh_C(N,S,C,Ind1,Expl,[Ind2|NI],ABox,Tabs,[(propertyAssertion(S,Ind1,Ind2),Expl),
                                          (classAssertion(C,Ind2),[propertyAssertion(S,Ind1,Ind2)|Expl])|ABox2],Tabs2):-
  N > 0,
  NoI is N-1,
  new_ind(Ind2),
  add_edge(S,Ind1,Ind2,Tabs,Tabs1),
  check_block(Ind2,([(propertyAssertion(S,Ind1,Ind2),Expl)|ABox],Tabs)),
  min_rule_neigh_C(NoI,S,C,Ind1,Expl,NI,ABox,Tabs1,ABox2,Tabs2).

%---------------------
safe_s_neigh([],_,_,[]).

safe_s_neigh([H|T],S,Tabs,[H|ST]):-
  safe(H,S,Tabs),
  safe_s_neigh(T,S,Tabs,ST).
/* **************** */

/*
  max_rule
  ================
*/
max_rule((ABox0,Tabs0),L):-
  findClassAssertion(maxCardinality(N,S,C),Ind,Expl,ABox0),
  \+ indirectly_blocked(Ind,(ABox0,Tabs0)),
  s_neighbours(Ind,S,(ABox0,Tabs0),SN),
  individual_class_C(SN,C,ABox0,SNC),
  length(SNC,LSS),
  LSS @> N,
  findall((ABox1,Tabs1),scan_max_list(S,SNC,Ind,Expl,ABox0,Tabs0, ABox1,Tabs1),L),
  dif(L,[]),
  !.

max_rule((ABox0,Tabs0),L):-
  findClassAssertion(maxCardinality(N,S),Ind,Expl,ABox0),
  \+ indirectly_blocked(Ind,(ABox0,Tabs0)),
  s_neighbours(Ind,S,(ABox0,Tabs0),SN),
  length(SN,LSS),
  LSS @> N,
  findall((ABox1,Tabs1),scan_max_list(S,SN,Ind,Expl,ABox0,Tabs0, ABox1,Tabs1),L),
  dif(L,[]),
  !.
%---------------------

scan_max_list(S,SN,Ind,Expl,ABox0,Tabs0,ABox,Tabs):-
  member(YI,SN),
  member(YJ,SN),
  check_individuals_not_equal(YI,YJ,ABox0),
  findPropertyAssertion(S,Ind,YI,ExplYI,ABox0),
  findPropertyAssertion(S,Ind,YJ,ExplYJ,ABox0),
  append(ExplYI,ExplYJ,Expl0),
  append(Expl,Expl0,ExplT),
  merge_all([(sameIndividual([YI,YJ]),ExplT)],ABox0,Tabs0,ABox,Tabs).

%--------------------
check_individuals_not_equal(X,Y,ABox):-
  dif(X,Y),
  \+ same_ind([X],Y,ABox).
%--------------------
individual_class_C([],_,_,[]).

individual_class_C([H|T],C,ABox,[H|T1]):-
  findClassAssertion(C,H,_,ABox),
  individual_class_C(T,C,ABox,T1).

individual_class_C([H|T],C,ABox,T1):-
  \+ findClassAssertion(C,H,_,ABox),
  individual_class_C(T,C,ABox,T1).
/* *************** */

/*
 o_rule
 ============
*/

o_rule((ABox0,Tabs0),([(sameIndividual(LI),ExplC)|ABox],Tabs)):-
  findClassAssertion(oneOf([C]),X,ExplX,ABox0),
  findClassAssertion(oneOf([D]),Y,ExplY,ABox0),
  containsCommon(C,D),
  dif(X,Y),
  notDifferentIndividuals(X,Y,ABox0),
  nominal(C,(ABox0,Tabs0)),
  indAsList(X,LX),
  indAsList(Y,LY),
  append(ExplX,ExplY,ExplC),
  merge(X,Y,(ABox0,Tabs0),(ABox,Tabs)),
  flatten([LX,LY],LI0),
  list_to_set(LI0,LI),
  absent(sameIndividual(LI),ExplC,(ABox0,Tabs0)).

containsCommon(L1,L2):-
  member(X,L1),
  member(X,L2),!.
% -------------------

indAsList(sameIndividual(L),L):-
  retract_sameIndividual(L),!.

indAsList(X,[X]):-
  atomic(X).

% -------------------
notDifferentIndividuals(X,Y,ABox):-
  \+ inAssertDifferentIndividuals(X,Y),
  \+ inABoxDifferentIndividuals(X,Y,ABox).

% --------------

inAssertDifferentIndividuals(differentIndividuals(X),differentIndividuals(Y)):-
  !,
  get_trill_current_module(Name),
  Name:differentIndividuals(LI),
  member(X0,X),
  member(X0,LI),
  member(Y0,Y),
  member(Y0,LI).

inAssertDifferentIndividuals(X,sameIndividual(Y)):-
  !,
  get_trill_current_module(Name),
  Name:differentIndividuals(LI),
  member(X,LI),
  member(Y0,Y),
  member(Y0,LI).

inAssertDifferentIndividuals(sameIndividual(X),Y):-
  !,
  get_trill_current_module(Name),
  Name:differentIndividuals(LI),
  member(X0,X),
  member(X0,LI),
  member(Y,LI).

inAssertDifferentIndividuals(X,Y):-
  get_trill_current_module(Name),
  Name:differentIndividuals(LI),
  member(X,LI),
  member(Y,LI).

% ------------------

inABoxDifferentIndividuals(sameIndividual(X),sameIndividual(Y),ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(X,sameIndividual(Y),ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(sameIndividual(X),Y,ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y,LI).

inABoxDifferentIndividuals(X,Y,ABox):-
  find((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y,LI).

% --------------------

listIntersection([],_,[]).

listIntersection([HX|TX],LCY,TI):-
  \+ member(HX,LCY),
  listIntersection(TX,LCY,TI).

listIntersection([HX|TX],LCY,[HX|TI]):-
  member(HX,LCY),
  listIntersection(TX,LCY,TI).

% ---------------

findExplForClassOf(LC,LI,ABox0,Expl):-
  member(C,LC),
  member(I,LI),
  findClassAssertion(C,I,Expl,ABox0).
%  member((classAssertion(C,I),Expl),ABox0).

/* ************ */


/*  absent
  =========
*/
absent(classAssertion(C,Ind),Expl,(ABox,_Tabs)):-
  \+ absent1(classAssertion(C,Ind),Expl,ABox),!.

absent(sameIndividual(L),Expl,(ABox,_Tabs)):-
  \+ absent1(sameIndividual(L),Expl,ABox),!.


%------------------
absent1(Ax,Expl,ABox):-
  find((Ax,Expl0),ABox),
  subset(Expl0,Expl),!.

absent1(sameIndividual(L),Expl,ABox):-
  find((sameIndividual(LF),Expl0),ABox),
  permutation(L,LF),
  subset(Expl0,Expl),!.

/* **************** */

/*
 * nominal/2, blockable/2, blocked/2, indirectly_blocked/2 and safe/3
 *
 */

nominal(Inds,(ABox,_)):-
  find((nominal(Ind)),ABox),
  member(Ind,Inds).

% ----------------

blockable(Ind,(ABox,_)):-
  ( find((nominal(Ind)),ABox)
    *->
    false
    ;
    true ).

% ---------------

blocked(Ind,(ABox,T)):-
  check_block(Ind,(ABox,T)).

/*

  control for block an individual

*/

check_block(Ind,(ABox,(T,RBN,RBR))):-
  blockable(Ind,(ABox,(T,RBN,RBR))),
  transpose_ugraph(T,T1),
  ancestor(Ind,T,A),
  neighbours(Ind,T1,N),
  check_block1(Ind,A,N,(ABox,(T1,RBN,RBR))),!.

check_block(Ind,(ABox,(T,RBN,RBR))):-
  blockable(Ind,(ABox,(T,RBN,RBR))),
  transpose_ugraph(T,T1),
  neighbours(Ind,T1,N),
  check_block2(N,(ABox,(T,RBN,RBR))),!.


check_block1(Indx,A,N,(ABox,(T,RBN,RBR))):-
  member(Indx0,N),
  member(Indy,A),
  member(Indy0,A),
  neighbours(Indy,T,N2),
  member(Indy0,N2),
  rb_lookup((Indx0,Indx),V,RBN),
  rb_lookup((Indy0,Indy),V2,RBN),
  member(R,V),
  member(R,V2),
  same_label(Indx,Indy0,ABox),
  same_label(Indx0,Indy,ABox),
  all_node_blockable(Indx0,Indy0,(ABox,(T,RBN,RBR))),!.

check_block2([],_).

check_block2([H|Tail],(ABox,(T,RBN,RBR))):-
  blocked(H,(ABox,(T,RBN,RBR))),
  check_block2(Tail,(ABox,(T,RBN,RBR))).

%---------------
indirectly_blocked(Ind,(ABox,(T,RBN,RBR))):-
  transpose_ugraph(T,T1),
  neighbours(Ind,T1,N),
  member(A,N),
  blocked(A,(ABox,(T,RBN,RBR))),!.

%---------------------
/*
  An R-neighbour y of a node x is safe if
  (i)  x is blockable or
  (ii) x is a nominal node and y is not blocked.
*/

safe(Ind,R,(ABox,(T,RBN,RBR))):-
  rb_lookup(R,V,RBR),
  member((X,Ind),V),
  blockable(X,(ABox,(T,RBN,RBR))),!.

safe(Ind,R,(ABox,(T,RBN,RBR))):-
  rb_lookup(R,V,RBR),
  member((X,Ind),V),
  nominal(X,(ABox,(T,RBN,RBR))),!,
  \+ blocked(Ind,(ABox,(T,RBN,RBR))).

/* ***** */

/*
 subset
 check if L is subset of L1
 =================

subset([],_).

subset([H|T],L):-
  member(H,L),
  subset(T,L).
*/

/*
 writel
 write a list one element at each line
 ==========
*/
writel([]):-!.

writel([T|C]):-
  write(T),nl,
  writel(C).

/*
 writeABox
 ==========
*/
writeABox((ABox,_)):-
  writel(ABox).


/*
  build_abox
  ===============
*/

/*build_abox(ABox):-
  findall((classAssertion(Class,Individual),[classAssertion(Class,Individual)]),classAssertion(Class,Individual),LCA),
  findall((propertyAssertion(Property,Subject, Object),[propertyAssertion(Property,Subject, Object)]),propertyAssertion(Property,Subject, Object),LPA),
  findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property,Subject,Object),propertyAssertion(SubProperty,Subject,Object)]),subPropertyOf(SubProperty,Property),LSPA),
  new_abox(ABox0),
  add_all(LCA,ABox0,ABox1),
  add_all(LPA,ABox1,ABox2),
  add_all(LSPA,ABox2,ABox).
*/

build_abox((ABox,Tabs)):-
  get_trill_current_module(Name),
  findall((classAssertion(Class,Individual),[classAssertion(Class,Individual)]),Name:classAssertion(Class,Individual),LCA),
  findall((propertyAssertion(Property,Subject, Object),[propertyAssertion(Property,Subject, Object)]),Name:propertyAssertion(Property,Subject, Object),LPA),
  findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(Name,SubProperty,Property,Subject,Object),LSPA),
  findall(nominal(NominalIndividual),Name:classAssertion(oneOf(_),NominalIndividual),LNA),
  new_abox(ABox0),
  new_tabs(Tabs0),
  create_tabs(LCA,Tabs0,Tabs1),
  add_all(LCA,ABox0,ABox1),
  add_all(LPA,ABox1,ABox2),
  add_all(LSPA,ABox2,ABox3),
  add_all(LNA,ABox3,ABox4),
  findall((differentIndividuals(Ld),[differentIndividuals(Ld)]),Name:differentIndividuals(Ld),LDIA),
  add_all(LDIA,ABox4,ABox5),
  create_tabs(LDIA,Tabs1,Tabs2),
  create_tabs(LPA,Tabs2,Tabs3),
  create_tabs(LSPA,Tabs3,Tabs4),
  findall((sameIndividual(L),[sameIndividual(L)]),Name:sameIndividual(L),LSIA),
  merge_all(LSIA,ABox5,Tabs4,ABox6,Tabs),
  add_nominal_list(ABox6,Tabs,ABox),
  !.

%---------------
subProp(Name,SubProperty,Property,Subject,Object):-
  Name:subPropertyOf(SubProperty,Property),Name:propertyAssertion(SubProperty,Subject,Object).

%--------------

add_nominal_list(ABox0,(T,_,_),ABox):-
  vertices(T,NomListIn),
  prepare_nom_list(NomListIn,NomListOut),
  add_all(NomListOut,ABox0,ABox).

%--------------

prepare_nom_list([],[]).

prepare_nom_list([H|T],[(nominal(H)),(classAssertion('Thing',H),[])|T1]):-
  prepare_nom_list(T,T1).
%--------------

/*
  add_all(L1,L2,LO).
  add in L2 all item of L1
*/
add_all([],A,A).

add_all([H|T],A0,A):-
  add(A0,H,A1),
  add_all(T,A1,A).

/* ************** */

/*
  initialize the tableau
  tableau is composed of:
  	a directed graph T => tableau without label
  	a red black tree RBN => each node is a couple of ind that contains the label for the edge
  	a red black tree RBR => each node a property that contains the couples of ind
*/
new_tabs(([],ItR,RtI)):-
  rb_new(ItR),
  rb_new(RtI).

create_tabs([],G,G).

create_tabs([(propertyAssertion(P,S,O),_Expl)|T],Tabl0,Tabl):-
  add_edge(P,S,O,Tabl0,Tabl1),
  create_tabs(T,Tabl1,Tabl).

create_tabs([(differentIndividuals(Ld),_Expl)|T],(T0,RBN,RBR),(T,RBN,RBR)):-
  add_vertices(T0,Ld,T).

create_tabs([(classAssertion(_,I),_Expl)|Tail],(T0,RBN,RBR),(T,RBN,RBR)):-
  add_vertices(T0,[I],T1),
  create_tabs(Tail,(T1,RBN,RBR),(T,RBN,RBR)).

create_tabs([(lpClassAssertion(_,I),_Expl)|Tail],(T0,RBN,RBR),(T,RBN,RBR)):-
  add_vertices(T0,[I],T1),
  create_tabs(Tail,(T1,RBN,RBR),(T,RBN,RBR)).


/*
  add edge to tableau

*/

add_edge(P,S,O,(T0,ItR0,RtI0),(T1,ItR1,RtI1)):-
  add_node_to_tree(P,S,O,ItR0,ItR1),
  add_role_to_tree(P,S,O,RtI0,RtI1),
  add_edge_to_tabl(P,S,O,T0,T1).

add_node_to_tree(P,S,O,RB0,RB1):-
  rb_lookup((S,O),V,RB0),
  \+ member(P,V),
  rb_update(RB0,(S,O),[P|V],RB1).

add_node_to_tree(P,S,O,RB0,RB0):-
  rb_lookup((S,O),V,RB0),
  member(P,V).

add_node_to_tree(P,S,O,RB0,RB1):-
  \+ rb_lookup([S,O],_,RB0),
  rb_insert(RB0,(S,O),[P],RB1).

add_role_to_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  \+ member((S,O),V),
  rb_update(RB0,P,[(S,O)|V],RB1).

add_role_to_tree(P,S,O,RB0,RB0):-
  rb_lookup(P,V,RB0),
  member((S,O),V).

add_role_to_tree(P,S,O,RB0,RB1):-
  \+ rb_lookup(P,_,RB0),
  rb_insert(RB0,P,[(S,O)],RB1).

add_edge_to_tabl(_R,Ind1,Ind2,T0,T0):-
  graph_edge(Ind1,Ind2,T0),!.

add_edge_to_tabl(_R,Ind1,Ind2,T0,T1):-
  add_edges(T0,[Ind1-Ind2],T1).

/*
  check for an edge
*/
graph_edge(Ind1,Ind2,T0):-
  edges(T0, Edges),
  member(Ind1-Ind2, Edges),!.

%graph_edge(_,_,_).

/*
  remove edge from tableau
*/

remove_node_to_tree(P,S,O,RB,RB):-
  rb_lookup((S,O),V,RB),
  \+ member(P,V).

remove_node_to_tree(P,S,O,RB0,RB1):-
  rb_lookup((S,O),V,RB0),
  member(P,V),
  remove(V,P,V1),
  dif(V1,[]),
  rb_update(RB0,(S,O),V1,RB1).

remove_node_to_tree(P,S,O,RB0,RB1):-
  rb_lookup((S,O),V,RB0),
  member(P,V),
  remove(V,P,V1),
  V1==[],
  rb_delete(RB0,(S,O),RB1).

remove_all_node_to_tree(_P,S,O,RB0,RB1):-
  rb_lookup((S,O),_,RB0),
  rb_delete(RB0,(S,O),RB1).

remove_all_node_to_tree(_P,S,O,RB0,_RB1):-
  \+ rb_lookup((S,O),_,RB0).

remove_role_to_tree(P,S,O,RB,RB):-
  rb_lookup(P,V,RB),
  \+ member((S,O),V).

remove_role_to_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  member((S,O),V),
  delete(V,(S,O),V1),
  dif(V1,[]),
  rb_update(RB0,P,V1,RB1).

remove_role_to_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  member((S,O),V),
  delete(V,(S,O),V1),
  V1==[],
  rb_delete(RB0,P,RB1).

remove_edge_to_table(_P,S,O,T,T):-
  \+ graph_edge(S,O,T).

remove_edge_to_table(_P,S,O,T0,T1):-
  graph_edge(S,O,T0),
  del_edges(T0,[S-O],T1).

remove_node_to_table(S,T0,T1):-
  del_vertices(T0,[S],T1).

/*
 * merge
 */
merge(sameIndividual(L),Y,(ABox0,Tabs0),(ABox,Tabs)):-
  !,
  merge_tabs(L,Y,Tabs0,Tabs),
  merge_abox(L,Y,[],ABox0,ABox).

merge(X,sameIndividual(L),(ABox0,Tabs0),(ABox,Tabs)):-
  !,
  merge_tabs(X,L,Tabs0,Tabs),
  merge_abox(X,L,[],ABox0,ABox).

merge(X,Y,(ABox0,Tabs0),(ABox,Tabs)):-
  !,
  merge_tabs(X,Y,Tabs0,Tabs),
  merge_abox(X,Y,[],ABox0,ABox).

/*
 * merge node in tableau
 */

merge_tabs(X,Y,(T0,RBN0,RBR0),(T,RBN,RBR)):-
  (neighbours(X,T0,LSX0)*->assign(LSX0,LSX);assign([],LSX)),
  (neighbours(Y,T0,LSY0)*->assign(LSY0,LSY);assign([],LSY)),
  transpose_ugraph(T0,TT),
  (neighbours(X,TT,LPX0)*->assign(LPX0,LPX);assign([],LPX)),
  (neighbours(Y,TT,LPY0)*->assign(LPY0,LPY);assign([],LPY)),
  flatten([X,Y],L0),
  list_to_set(L0,L),
  set_predecessor(L,X,LPX,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),!,
  set_successor(L,X,LSX,(T1,RBN1,RBR1),(T2,RBN2,RBR2)),!,
  set_predecessor(L,Y,LPY,(T2,RBN2,RBR2),(T3,RBN3,RBR3)),!,
  set_successor(L,Y,LSY,(T3,RBN3,RBR3),(T4,RBN4,RBR4)),!,
  remove_nodes(X,Y,(T4,RBN4,RBR4),(T,RBN,RBR)).

remove_nodes(X,Y,Tabs0,Tabs):-
  remove_node(X,Tabs0,Tabs1),
  remove_node(Y,Tabs1,Tabs).

remove_node(X,(T0,RBN0,RBR0),(T,RBN,RBR)):-
  (neighbours(X,T0,LS0)*->assign(LS0,LS);assign([],LS)),
  transpose_ugraph(T0,TT),
  (neighbours(X,TT,LP0)*->assign(LP0,LP);assign([],LP)),
  remove_node1(X,LS,RBN0,RBR0,RBN1,RBR1),
  remove_node2(X,LP,RBN1,RBR1,RBN,RBR),
  (vertices(T0,VS),member(X,VS)*->del_vertices(T0,[X],T);assign(T0,T)).

remove_node1(_,[],RBN,RBR,RBN,RBR).

remove_node1(X,[H|T],RBN0,RBR0,RBN,RBR):-
  rb_lookup((X,H),V,RBN0),
  remove_edges(V,X,H,RBR0,RBR1),
  remove_all_node_to_tree(_,X,H,RBN0,RBN1),
  remove_node1(X,T,RBN1,RBR1,RBN,RBR).

remove_node2(_,[],RBN,RBR,RBN,RBR).

remove_node2(X,[H|T],RBN0,RBR0,RBN,RBR):-
  rb_lookup((H,X),V,RBN0),
  remove_edges(V,H,X,RBR0,RBR1),
  remove_all_node_to_tree(_,H,X,RBN0,RBN1),
  remove_node1(X,T,RBN1,RBR1,RBN,RBR).

remove_edges([],_,_,RBR,RBR).

remove_edges([H|T],S,O,RBR0,RBR):-
  remove_role_to_tree(H,S,O,RBR0,RBR1),
  remove_edges(T,S,O,RBR1,RBR).


set_predecessor(_NN,_,[],Tabs,Tabs).

set_predecessor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  rb_lookup((H,X),LR,RBN0),
  set_predecessor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_predecessor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_predecessor1(_NN,_H,[],Tabs,Tabs).

set_predecessor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  add_edge(R,H,NN,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_predecessor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_successor(_NN,_X,[],Tabs,Tabs).

set_successor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  rb_lookup((X,H),LR,RBN0),
  set_successor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_successor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_successor1(_NN,_H,[],Tabs,Tabs).

set_successor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  add_edge(R,NN,H,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_successor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

/*
  merge node in ABox
*/

merge_abox(_X,_Y,_,[],[]).

merge_abox(X,Y,Expl0,[(classAssertion(C,Ind),ExplT)|T],[(classAssertion(C,sameIndividual(L)),[sameIndividual(L)|Expl])|ABox]):-
  flatten([X,Y],L0),
  list_to_set(L0,L),
  member(Ind,L),!,
  append(Expl0,ExplT,Expl),
  merge_abox(X,Y,Expl0,T,ABox).

merge_abox(X,Y,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,sameIndividual(L),Ind2),[sameIndividual(L)|Expl])|ABox]):-
  flatten([X,Y],L0),
  list_to_set(L0,L),
  member(Ind1,L),!,
  append(Expl0,ExplT,Expl),
  merge_abox(X,Y,Expl0,T,ABox).

merge_abox(X,Y,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,Ind1,sameIndividual(L)),[sameIndividual(L)|Expl])|ABox]):-
  flatten([X,Y],L0),
  list_to_set(L0,L),
  member(Ind2,L),!,
  append(Expl0,ExplT,Expl),
  merge_abox(X,Y,Expl0,T,ABox).

merge_abox(X,Y,Expl0,[H|T],[H|ABox]):-
  merge_abox(X,Y,Expl0,T,ABox).

/* merge node in (ABox,Tabs) */

merge_all([],ABox,Tabs,ABox,Tabs).

merge_all([(sameIndividual(H),Expl)|T],ABox0,Tabs0,ABox,Tabs):-
  find_same(H,ABox0,L,ExplL),
  dif(L,[]),!,
  merge_all1(H,L,ABox0,Tabs0,ABox1,Tabs1),
  flatten([H,L],L0),
  list_to_set(L0,L1),
  append(Expl,ExplL,ExplT),
  add(ABox1,(sameIndividual(L1),ExplT),ABox2),
  delete(ABox2,(sameIndividual(L),ExplL),ABox3),
  retract_sameIndividual(L),
  merge_all(T,ABox3,Tabs1,ABox,Tabs).

merge_all([(sameIndividual(H),Expl)|T],ABox0,Tabs0,ABox,Tabs):-
  find_same(H,ABox0,L,_),
  L==[],!,
  merge_all2(H,ABox0,Tabs0,ABox1,Tabs1),
  add(ABox1,(sameIndividual(H),Expl),ABox2),
  merge_all(T,ABox2,Tabs1,ABox,Tabs).

merge_all1([],_,ABox,Tabs,ABox,Tabs).

merge_all1([H|T],L,ABox0,Tabs0,ABox,Tabs):-
  \+ member(H,L),
  merge(H,L,(ABox0,Tabs0),(ABox1,Tabs1)),
  merge_all1(T,[H|L],ABox1,Tabs1,ABox,Tabs).

merge_all1([H|T],L,ABox0,Tabs0,ABox,Tabs):-
  member(H,L),
  merge_all1(T,L,ABox0,Tabs0,ABox,Tabs).



merge_all2([X,Y|T],ABox0,Tabs0,ABox,Tabs):-
  merge(X,Y,(ABox0,Tabs0),(ABox1,Tabs1)),
  merge_all1(T,[X,Y],ABox1,Tabs1,ABox,Tabs).

find_same(H,ABox,L,Expl):-
  find((sameIndividual(L),Expl),ABox),
  member(X,L),
  member(X,H),!.

find_same(_H,_ABox,[],[]).

/* abox as a list */

new_abox([]).


/* add El to ABox */
add(ABox,El,[El|ABox]).

assign(L,L).
/*
  find & control (not find)
*/
find(El,ABox):-
  member(El,ABox).

control(El,ABox):-
  \+ find(El,ABox).

/* end of abox a s list */

/* abox as a red-black tree */
/*new_abox(T):-
  rb_new(T).

add(A,(Ass,Ex),A1):-
  rb_insert(A,(Ass,Ex),[],A1).

find((Ass,Ex),A):-
  rb_lookup((Ass,Ex),_,A).
*/
/* end of abox as a rb tree */

/*
  creation of a new individual

*/
new_ind(I):-
  retract(ind(I)),
  I1 is I+1,
  assert(ind(I1)).



/*
  same label for two individuals

*/

same_label(X,Y,ABox):-
  \+ different_label(X,Y,ABox),
  !.

/*

 different label in two individuals

*/

different_label(X,Y,ABox):-
  findClassAssertion(C,X,_,ABox),
  \+ findClassAssertion(C,Y,_,ABox).

different_label(X,Y,ABox):-
  findClassAssertion(C,Y,_,ABox),
  \+ findClassAssertion(C,X,_,ABox).


/*
  all nodes in path from X to Y are blockable?

*/

all_node_blockable(X,Y,(ABox,(T,RBN,RBR))):-
  graph_min_path(X,Y,T,P),
  all_node_blockable1(P,(ABox,(T,RBN,RBR))).

all_node_blockable1([],_).

all_node_blockable1([H|Tail],(ABox,(T,RBN,RBR))):-
  blockable(H,(ABox,(T,RBN,RBR))),
  all_node_blockable1(Tail,(ABox,(T,RBN,RBR))).

/*
  find a path in the graph
*/
graph_min_path(X,Y,T,P):-
  findall(Path, graph_min_path1(X,Y,T,Path), Ps),
  min_length(Ps,P).

graph_min_path1(X,Y,T,[X,Y]):-
  member(X-L,T),
  member(Y,L).

graph_min_path1(X,Y,T,[X|P]):-
  member(X-L,T),
  member(Z,L),
  graph_min_path1(Z,Y,T,P).

min_length([H],H).

min_length([H|T],MP):-
  min_length(T,P),
  length(H,N),
  length(P,NP),
  (N<NP *->
     MP= H
   ;
     MP= P).
/*
 find all ancestor of a node

*/
ancestor(Ind,T,AN):-
  transpose_ugraph(T,T1),
  ancestor1([Ind],T1,[],AN).

ancestor1([],_,A,A).

ancestor1([Ind|Tail],T,A,AN):-
  neighbours(Ind,T,AT),
  add_all_n(AT,Tail,Tail1),
  add_all_n(A,AT,A1),
  ancestor1(Tail1,T,A1,AN).

%-----------------
/*

 add_all_n(L1,L2,LO)
 add in L2 all item of L1 without duplicates

*/

add_all_n([],A,A).

add_all_n([H|T],A,AN):-
  \+ member(H,A),
  add_all_n(T,[H|A],AN).

add_all_n([H|T],A,AN):-
  member(H,A),
  add_all_n(T,A,AN).
/* *************** */

/*
 retract_sameIndividual(L)
 ==========
*/
retract_sameIndividual(L):-
  get_trill_current_module(N),
  retract(N:sameIndividual(L)).

retract_sameIndividual(L):-
  get_trill_current_module(N),
  \+ retract(N:sameIndividual(L)).
/* ****** */

/*
  find all S neighbours (S is a role)
*/
s_neighbours(Ind1,S,(ABox,(_,_,RBR)),SN):-
  rb_lookup(S,VN,RBR),
  s_neighbours1(Ind1,VN,SN1),
  s_neighbours2(SN1,SN1,SN,ABox).

s_neighbours(_Ind1,S,(_,_,RBR),[]):-
  \+ rb_lookup(S,_VN,RBR).

s_neighbours1(_,[],[]).

s_neighbours1(Ind1,[(Ind1,Y)|T],[Y|T1]):-
  s_neighbours1(Ind1,T,T1).

s_neighbours1(Ind1,[(X,_Y)|T],T1):-
  dif(X,Ind1),
  s_neighbours1(Ind1,T,T1).

s_neighbours2(_,[],[],_).

s_neighbours2(SN,[H|T],[H|T1],ABox):-
  s_neighbours2(SN,T,T1,ABox),
  \+ same_ind(T1,H,ABox).

s_neighbours2(SN,[H|T],T1,ABox):-
  s_neighbours2(SN,T,T1,ABox),
  same_ind(T1,H,ABox).

%-----------------
same_ind(SN,H,_ABox):-
  get_trill_current_module(Name),
  Name:sameIndividual(SI),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2).

same_ind(SN,H,ABox):-
  find((sameIndividual(SI),_),ABox),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2).

/* ************* */

/*
 s_predecessors
 ==============
 find all S-predecessor of Ind
*/

s_predecessors(Ind1,S,(ABox,(_,_,RBR)),SN):-
  rb_lookup(S,VN,RBR),
  s_predecessors1(Ind1,VN,SN1),
  s_predecessors2(SN1,SN,ABox).

s_predecessors(_Ind1,S,(_ABox,(_,_,RBR)),[]):-
  \+ rb_lookup(S,_VN,RBR).

s_predecessors1(_,[],[]).

s_predecessors1(Ind1,[(Y,Ind1)|T],[Y|T1]):-
  s_predecessors1(Ind1,T,T1).

s_predecessors1(Ind1,[(_X,Y)|T],T1):-
  dif(Y,Ind1),
  s_predecessors1(Ind1,T,T1).

s_predecessors2([],[],_).

s_predecessors2([H|T],[H|T1],ABox):-
  s_predecessors2(T,T1,ABox),
  \+ same_ind(T1,H,ABox).

s_predecessors2([H|T],T1,ABox):-
  s_predecessors2(T,T1,ABox),
  same_ind(T1,H,ABox).

/* ********** */

/* *************
   Probability computation

   ************* */

/*
build_formula([],[],Var,Var).

build_formula([D|TD],TF,VarIn,VarOut):-
        build_term(D,[],[],VarIn,Var1),!,
        build_formula(TD,TF,Var1,VarOut).

build_formula([D|TD],[F|TF],VarIn,VarOut):-
        build_term(D,[],F,VarIn,Var1),
        build_formula(TD,TF,Var1,VarOut).

build_term([],F,F,Var,Var).

build_term([(Ax,S)|TC],F0,F,VarIn,VarOut):-!,
  (p_x(Ax,_)*->
    (nth0_eq(0,NVar,VarIn,(Ax,S))*->
      Var1=VarIn
    ;
      append(VarIn,[(Ax,S)],Var1),
      length(VarIn,NVar)
    ),
    build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
  ;
    (p(Ax,_)*->
      (nth0_eq(0,NVar,VarIn,(Ax,[]))*->
        Var1=VarIn
      ;
        append(VarIn,[(Ax,[])],Var1),
        length(VarIn,NVar)
      ),
      build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
    ;
      build_term(TC,F0,F,VarIn,VarOut)
    )
  ).

build_term([Ax|TC],F0,F,VarIn,VarOut):-!,
  (p(Ax,_)*->
    (nth0_eq(0,NVar,VarIn,(Ax,[]))*->
      Var1=VarIn
    ;
      append(VarIn,[(Ax,[])],Var1),
      length(VarIn,NVar)
    ),
    build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
  ;
    build_term(TC,F0,F,VarIn,VarOut)
  ).
*/

/* nth0_eq(PosIn,PosOut,List,El) takes as input a List,
an element El and an initial position PosIn and returns in PosOut
the position in the List that contains an element exactly equal to El
*/

/*
nth0_eq(N,N,[H|_T],El):-
        H==El,!.

nth0_eq(NIn,NOut,[_H|T],El):-
        N1 is NIn+1,
        nth0_eq(N1,NOut,T,El).

*/
/* var2numbers converts a list of couples (Rule,Substitution) into a list
of triples (N,NumberOfHeadsAtoms,ListOfProbabilities), where N is an integer
starting from 0 */
/*
var2numbers([],_N,[]).

var2numbers([(R,_S)|T],N,[[N,2,[Prob,Prob1,0.3,0.7]]|TNV]):-
        (p(R,_);p_x(R,_)),
        compute_prob_ax(R,Prob),!,
        Prob1 is 1-Prob,
        N1 is N+1,
        var2numbers(T,N1,TNV).


compute_prob_ax(R,Prob):-
  findall(P, p(R,P),Probs),
  compute_prob_ax1(Probs,Prob).

compute_prob_ax1([Prob],Prob):-!.

compute_prob_ax1([Prob1,Prob2],Prob):-!,
  Prob is Prob1+Prob2-(Prob1*Prob2).

compute_prob_ax1([Prob1 | T],Prob):-
  compute_prob_ax1(T,Prob0),
  Prob is Prob1 + Prob0 - (Prob1*Prob0).

*/

/**********************

TRILL COMPUTEPROB

***********************/
/*
:- thread_local
	%get_var_n/5,
        rule_n/1,
        na/2,
        v/3.

%rule_n(0).

compute_prob(Expl,Prob):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  get_trill_current_module(Name),
  findall(1,Name:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  init_test(NV,Env),
  build_bdd(Env,Expl,BDD),
  ret_prob(Env,BDD,Prob),
  end_test(Env), !.



build_bdd(Env,[X],BDD):- !,
  bdd_and(Env,X,BDD).

build_bdd(Env, [H|T],BDD):-
  build_bdd(Env,T,BDDT),
  bdd_and(Env,H,BDDH),
  or(Env,BDDH,BDDT,BDD).

build_bdd(Env,[],BDD):- !,
  zero(Env,BDD).


bdd_and(Env,[nbf(Expl)],BDDNeg):-!,
  bdd_and(Env,Expl,BDD2Neg),
  bdd_not(Env,BDD2Neg,BDDNeg).

bdd_and(Env,[X],BDDX):-
  get_prob_ax(X,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VX),
  equality(Env,VX,0,BDDX),!.

bdd_and(Env,[_X],BDDX):- !,
  one(Env,BDDX).

bdd_and(Env,[nbf(Expl)|T],BDDAnd):-
  bdd_and(Env,Expl,BDD2Neg),
  bdd_not(Env,BDD2Neg,BDDNeg),
  bdd_and(Env,T,BDDT),
  and(Env,BDDNeg,BDDT,BDDAnd).

bdd_and(Env,[H|T],BDDAnd):-
  get_prob_ax(H,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VH),
  equality(Env,VH,0,BDDH),
  bdd_and(Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).

bdd_and(Env,[_H|T],BDDAnd):- !,
  one(Env,BDDH),
  bdd_and(Env,T,BDDT),
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


get_prob_ax((Ax,_Ind),N,Prob):- !,
  compute_prob_ax(Ax,Prob),
  ( na(Ax,N) ->
      true
    ;
      rule_n(N),
      assert(na(Ax,N)),
      retract(rule_n(N)),
      N1 is N + 1,
      assert(rule_n(N1))
  ).
get_prob_ax(Ax,N,Prob):- !,
  compute_prob_ax(Ax,Prob),
  ( na(Ax,N) ->
      true
    ;
      rule_n(N),
      assert(na(Ax,N)),
      retract(rule_n(N)),
      N1 is N + 1,
      assert(rule_n(N1))
  ).

compute_prob_ax(Ax,Prob):-
  get_trill_current_module(Name),
  findall(ProbA,(Name:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(ProbAT)),atom_number(ProbAT,ProbA)),Probs),
  compute_prob_ax1(Probs,Prob).

compute_prob_ax1([Prob],Prob):-!.

compute_prob_ax1([Prob1,Prob2],Prob):-!,
  Prob is Prob1+Prob2-(Prob1*Prob2).

compute_prob_ax1([Prob1 | T],Prob):-
  compute_prob_ax1(T,Prob0),
  Prob is Prob1 + Prob0 - (Prob1*Prob0).
*/
/************************/

/**************/
/*get_trill_current_module('translate_rdf'):-
  pengine_self(_Name),!.*/
%get_trill_current_module(Name):-
%  pengine_self(Name),!.
get_trill_current_module('owl2_model'):- !.
/**************/

:- multifile sandbox:safe_primitive/1.
/*
sandbox:safe_primitive(trill:init_test(_,_)).
sandbox:safe_primitive(trill:ret_prob(_,_,_)).
sandbox:safe_primitive(trill:end_test(_)).
sandbox:safe_primitive(trill:one(_,_)).
sandbox:safe_primitive(trill:zero(_,_)).
sandbox:safe_primitive(trill:and(_,_,_,_)).
sandbox:safe_primitive(trill:or(_,_,_,_)).
sandbox:safe_primitive(trill:bdd_not(_,_,_)).
sandbox:safe_primitive(trill:get_var_n(_,_,_,_,_)).
sandbox:safe_primitive(trill:add_var(_,_,_,_,_)).
sandbox:safe_primitive(trill:equality(_,_,_,_)).
*/

sandbox:safe_primitive(trill:sub_class(_,_)).
sandbox:safe_primitive(trill:sub_class(_,_,_)).
sandbox:safe_primitive(trill:prob_sub_class(_,_,_)).
sandbox:safe_primitive(trill:instanceOf(_,_)).
sandbox:safe_primitive(trill:instanceOf(_,_,_)).
sandbox:safe_primitive(trill:prob_instanceOf(_,_,_)).
sandbox:safe_primitive(trill:property_value(_,_,_)).
sandbox:safe_primitive(trill:property_value(_,_,_,_)).
sandbox:safe_primitive(trill:prob_property_value(_,_,_,_)).
sandbox:safe_primitive(trill:unsat(_)).
sandbox:safe_primitive(trill:unsat(_,_)).
sandbox:safe_primitive(trill:prob_unsat(_,_)).
sandbox:safe_primitive(trill:inconsistent_theory).
sandbox:safe_primitive(trill:inconsistent_theory(_)).
sandbox:safe_primitive(trill:prob_inconsistent_theory(_)).
sandbox:safe_primitive(trill:axiom(_)).
sandbox:safe_primitive(trill:add_kb_prefix(_,_)).
sandbox:safe_primitive(trill:add_axiom(_)).
sandbox:safe_primitive(trill:add_axioms(_)).
sandbox:safe_primitive(trill:load_kb(_)).
sandbox:safe_primitive(trill:load_owl_kb(_)).
sandbox:safe_primitive(trill:build_and_expand(_)).
sandbox:safe_primitive(trill:instanceOf_meta(_,_,_)).
sandbox:safe_primitive(trill:property_value_meta(_,_,_,_)).

:- use_module(translate_rdf).

:- if(\+pengine_self(_Name)).
:- trill.
:- endif.

