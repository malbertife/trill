%%
% LPAD
%%
notMarried(X) :- person(X), \+ married(X)
discount(X) :- spouse(X,Y), person(X), person(Y).


%%
% KB
%%
equivalentClasses([notMarried,complementOf(married)]).
subClassOf(notMarried,highRisk).
annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',subClassOf(notMarried,highRisk),literal('0.4'))
subClassOf(someValuesFrom(spouse,'Thing'),married).
classAssertion(person,john).
