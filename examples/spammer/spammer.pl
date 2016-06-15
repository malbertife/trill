%%
% LPAD
%%
spammer(X) :- hasReports(X), nbf(trustedUser(X)).
rejected(X,Y) :- invited(X,Y), nbf(accepted(Y,X)).


%%
% KB
%%
owl2_model:subClassOf(someValuesFrom(rejected,'Thing'),spammer).
owl2_model:subClassOf(minCardinality(3,reported),hasReports).
%owl2_model:subClassOf(minCardinality(3,reported,'Thing'),hasReports).
owl2_model:subClassOf(someValuesFrom(reported,trustedUser),hasReports).
owl2_model:propertyAssertion(invited,john,mary).

owl2_model:lpClassAssertion(spammer).
