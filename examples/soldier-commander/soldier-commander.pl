
%%
% LPAD
%%
soldier(X) :- guard(X).


%%
% KB
%%
subClassOf(allValuesFrom(commands,soldier),commander).
classAssertion(guard,pete).
classAssertion(guard,al).
classAssertion(allValuesFrom(commands,guard),john).

%owl2_model:lpClassAssertion(soldier).


/*
%%
% LPAD
%%
soldier(X) :- person(X), guard(X).
person(pete).
person(al).
person(john).

%%
% KB
%%
owl2_model:subClassOf(allValuesFrom(commands,soldier),commander).
owl2_model:classAssertion(guard,pete).
owl2_model:classAssertion(guard,al).
owl2_model:classAssertion(allValuesFrom(commands,guard),john).

owl2_model:lpClassAssertion(soldier).
*/
