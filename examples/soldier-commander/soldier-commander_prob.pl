%%
% LPAD
%%
soldier(X):0.8 :- person(X),guard(X).
person(pete).
person(al).
person(john).


%%
% KB
%%
subClassOf(allValuesFrom(commands,soldier),commander).
classAssertion(guard,pete).
classAssertion(guard,al).
propertyAssertion(commands,john,pete).
propertyAssertion(commands,john,al).
classAssertion(allValuesFrom(commands,guard),john).
