
z(X):-w(X,Y),k(Y).

subClassOf(someValuesFrom(s,e),f).

s(X,Y):-r(X,Y).
e(X):-d(X).

subClassOf(c,someValuesFrom(r,d)).

c(X):-b(X).

subClassOf(a,b).
classAssertion(a,i).

owl2_model:lpClassAssertion(c).
owl2_model:lpClassAssertion(e).
owl2_model:lpPropertyAssertion(s).
