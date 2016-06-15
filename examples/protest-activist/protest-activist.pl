%%
% LPAD
%%
protest :- activist(X), nbf(cruelToAnimals(X)).

activist(kevin).
asctivist(nadia).


%%
% KB
%%
owl2_model:subClassOf(someValuesFrom(hasAnimal,pet),complementOf(cruelToAnimals)).
owl2_model:propertyAssertion(hasAnimal,kevin,fluffy).
owl2_model:subClassOf(cat,pet).
owl2_model:classAssertion(cat,fluffy).

owl2_model:lpClassAssertion(cat).
