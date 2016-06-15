%%
% LPAD
%%
soldier(X) :- guard(X).


%%
% KB
%%
owl2_model:subClassOf(someValuesFrom(commands,soldier),commander).
owl2_model:classAssertion(guard,pete).
owl2_model:classAssertion(guard,al).
owl2_model:classAssertion(someValuesFrom(commands,guard),john).

owl2_model:lpClassAssertion(soldier).
