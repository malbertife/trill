%%
% LPAD
%%
notMarried(X) :- person(X), nbf(married(X)).
discount(X) :- spouse(X,Y), person(X), person(Y).


%%
% KB
%%
owl2_model:equivalentClasses([notMarried,complementOf(married)]).
owl2_model:subClassOf(notMarried,highRisk).
owl2_model:subClassOf(someValuesFrom(spouse,'Thing'),married).
owl2_model:classAssertion(person,john).
owl2_model:classAssertion(married,john).

owl2_model:lpClassAssertion(notMarried).
owl2_model:lpClassAssertion(discount).