%%
% LPAD
%%
protest:0.6 :- activist(X), \+ cruelToAnimals(X).

activist(kevin).
asctivist(nadia):0.3.


%%
% KB
%%
owl2_model:subClassOf(someValuesFrom(hasAnimal,pet),complementOf(cruelToAnimals)).
owl2_model:propertyAssertion(hasAnimal,kevin,fluffy).
owl2_model:subClassOf(cat,pet).
owl2_model:classAssertion(cat,fluffy).
owl2_model:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',classAssertion(cat,fluffy),literal('0.3'))
