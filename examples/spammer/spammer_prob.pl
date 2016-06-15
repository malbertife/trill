%%
% LPAD
%%
spammer(X):0.3 :- hasReports(X), \+ trustedUser(X)
rejected(X,Y) :- invited(X,Y), \+accepted(Y,X).


%%
% KB
%%
owl2_model:subClassOf(someValuesFrom(rejected,'Thing'),spammer).
owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',subClassOf(someValuesFrom(rejected,'Thing'),spammer),literal('0.4'))
owl2_model:subClassOf(minCardinality(3,reported),hasReports).
%owl2_model:subClassOf(minCardinality(3,reported,'Thing'),hasReports).
owl2_model:subClassOf(someValuesFrom(reported,trustedUser),hasReports).
