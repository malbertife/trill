%%
% LPAD
%%
soldier(X) :- guard(X).


%%
% KB
%%
owl2_model:subClassOf(allValuesFrom(commands,soldier),commander).
owl2_model:classAssertion(guard,pete).
owl2_model:classAssertion(guard,al).
owl2_model:classAssertion(allValuesFrom(commands,guard),john).

owl2_model:lpClassAssertion(soldier).
