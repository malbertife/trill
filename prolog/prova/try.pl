
z(X):-w(X,Y),k(Y).

subClassOf(someValuesFrom(s,e),f).

s(X,Y):-r1(X,Y).
r1(X,Y):-r2(X,Y).
r2(X,Y):-r(X,Y).
e(X):-d1(X).
%e(X):-m(X).
d1(X):-d(X).
%m(X):-d(X).

subClassOf(c,someValuesFrom(r,d)).

c(X):-b(X).

subClassOf(a,b).
subClassOf(a,a1).
subClassOf(a1,b).
classAssertion(a,i).

owl2_model:lpClassAssertion(c).
owl2_model:lpClassAssertion(e).
owl2_model:lpPropertyAssertion(s).
