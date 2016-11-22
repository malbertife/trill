#!/bin/bash

if [ "$#" -ne 1 ]; then
    echo "Illegal number of parameters: please specify output file"
    exit
fi

cd examples
echo "Start test..."

# Ceremony
cd ceremony
echo "Ceremony DL"
echo "Ceremony DL: " > ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(ceremony,'ceremony_dl',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('ceremony_dl'),prob(ceremony,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('ceremony_dl'),prob(ceremony,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

echo "Ceremony PL"
echo "Ceremony PL: " >> ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(ceremony,'ceremony_pl',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('ceremony_pl'),prob(ceremony,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('ceremony_pl'),prob(ceremony,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

# Married
cd ../married
echo "Married"
echo "Married: " >> ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(highRisk(john),'married_prob',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('married_prob'),prob(highRisk(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('married_prob'),prob(highRisk(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

# Protest activist
cd ../protest-activist
echo "Protest Activist"
echo "Protest Activist: " >> ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(protest,'protest-activist_prob',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('protest-activist_prob'),prob(protest,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('protest-activist_prob'),prob(protest,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

# Soldier commander
cd ../soldier-commander
echo "Soldier Commander"
echo "Soldier Commander: " >> ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(commander(john),'soldier-commander_prob',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('soldier-commander_prob'),prob(commander(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('soldier-commander_prob'),prob(commander(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

# Spammer
cd ../spammer
echo "Spammer"
echo "Spammer: " >> ../../$1
echo "- semphkb: " >> ../../$1
echo "S is cputime,s(spammer(john),'spammer_prob',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/semphkb/semphkb.pl >> ../../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../../$1
echo "S is cputime,p('spammer_prob'),prob(spammer(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova/metainterprete_lpadsld.pl >> ../../$1

echo "- prova_2/metainterprete.pl: " >> ../../$1
echo "S is cputime,p('spammer_prob'),prob(spammer(john),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../../prolog/prova_2/metainterprete.pl >> ../../$1

# Coin
cd ..
echo "Coin"
echo "Coin: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(heads(coin),'coin',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p('coin'),prob(heads(coin),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p('coin'),prob(heads(coin),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

# Monty
echo "Monty"
echo "Monty: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(win_switch,'monty',P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p('monty'),prob(win_switch,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p('monty'),prob(win_switch,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

# Try files 1-8
echo "Try 1"
echo "Try 1: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 2"
echo "Try 2: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try2,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try2),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try2),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 3"
echo "Try 3: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try3,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try3),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try3),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 4"
echo "Try 4: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try4,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try4),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try4),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 5"
echo "Try 5: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try5,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try5),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try5),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 6"
echo "Try 6: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(f(i),try6,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try6),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try6),prob(f(i),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 7"
echo "Try 7: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(g(a),try7,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try7),prob(g(a),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try7),prob(g(a),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

echo "Try 8"
echo "Try 8: " >> ../$1
echo "- semphkb: " >> ../$1
echo "S is cputime,s(g(a),try8,P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/semphkb/semphkb.pl >> ../$1

echo "- prova/metainterprete_lpadsld.pl: " >> ../$1
echo "S is cputime,p(try8),prob(g(a),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova/metainterprete_lpadsld.pl >> ../$1

echo "- prova_2/metainterprete.pl: " >> ../$1
echo "S is cputime,p(try8),prob(g(a),P),E is cputime, T is E-S,format('   P: ~f~n   T: ~f~n',[P,T]),halt."| swipl ../prolog/prova_2/metainterprete.pl >> ../$1

