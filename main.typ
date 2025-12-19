#import "@preview/grape-suite:3.1.0": seminar-paper, german-dates, citation
#import seminar-paper: important-box, brown, magenta
#import citation: *
#import "@preview/simplebnf:0.1.1": bnf, Prod, Or
#import "@preview/curryst:0.5.1": rule, prooftree

#set text(lang: "en")

#let standard-box-translations = (
    "definition": [Définition],
    "notice": [Remarque],
    "example": [Exemple],
    "theorem": [Théorème],
)

#let definition = important-box.with(
    title: context state("grape-suite-box-translations", standard-box-translations).final().at("definition"),
    primary-color: magenta,
    secondary-color: magenta.lighten(90%),
    tertiary-color: magenta,
    figure-kind: "definition",
    counter: counter("grape-suite-element-definition"))

#let theorem = important-box.with(
    title: context state("grape-suite-box-translations", standard-box-translations).final().at("theorem"),
    primary-color: red,
    secondary-color: red.lighten(90%),
    tertiary-color: red,
    figure-kind: "theorem",
    counter: counter("grape-suite-element-definition"))

#let notice = important-box.with(
    title: context state("grape-suite-box-translations", standard-box-translations).final().at("notice"),
    primary-color: blue,
    secondary-color: blue.lighten(90%),
    tertiary-color: blue,
    dotted: true,
    figure-kind: "notice",
    counter: counter("grape-suite-element-notice"))

#let example = important-box.with(
    title: context state("grape-suite-box-translations", standard-box-translations).final().at("example"),
    primary-color: yellow,
    secondary-color: yellow.lighten(90%),
    tertiary-color: brown,
    dotted: true,
    figure-kind: "example",
    counter: counter("grape-suite-element-example"))

#let definition = definition.with(figured: true)

#show: seminar-paper.project.with(
    title: "Interprétation Abstraite du langage Rust",
    subtitle: "",

    university: [Télécom SudParis, LIP6],
    faculty: [],
    institute: [],
    docent: [],
    seminar: [],

    submit-to: [],
    submit-by: [],

    semester: "",

    author: "Augustin PERRIN",
    email: "augustin.perrin@telecom-sudparis.eu",
    address: [
    ],

    show-declaration-of-independent-work: false
)

#let eq_def(e1, e2) = {
    [#e1$eq.delta$#e2]
}

= Sous-ensemble du langage Rust (Mid-level Intermediate Representation)

== Grammaire <grammar>

On travaille sur la grammaire formelle suivante, du pseudo langage qu'on appelle $lambda_"MIR"$ :
#bnf(
    Prod("s",
    delim : $::=$,
    annot: $sans("Instruction")$,
    {
        Or[`storage_live`($v$ : $tau$)][_création de variable_]
        Or[`storage_dead`($v$ : $tau$)][_suppression de variable_]
        Or[$e = e$][_affectation_]
        Or[$v = $ `&mut` $v$][_emprunt mutable_]
        Or[$v = $ `&`$v$][_référence partagée_]
        Or[$v = $ `move`$(v)$][_transfert d'appartenance_]
        Or[$s$;$s$][_chainage d'instructions_]
        Or[`loop`$(i in NN) { s }$][_boucle (imbrication $i in NN$)_]
        Or[`break`$(i in NN)$][_terminateur de boucle_]
        Or[`if`$(c) { s }$ `else` ${ s }$][_conditionnelle_]
        Or[`()`][_instruction vide_]
    }),
    Prod("e",
    delim : $::=$,
    annot: $sans("Expression")$,
    {
        Or[`copy`$(e)$][_copie_]
        Or[$v in cal(V)$][_variable_]
        Or[$z in ZZ$][_constante_]
        Or[$e$ $bullet.stroked.o$ $e$][_opérateur binaire_]
        Or[$[z_1 in ZZ union {-infinity};z_2 in ZZ union {+infinity}]$][_non déterminisme_]
        Or[$*e$][_déréférence_]
    }),
    Prod("c",
    delim : $::=$,
    annot : $sans("Condition")$,
    {
        Or[$e ast.op.o e$][_comparateur binaire_]
        Or[$!(c)$][_négation_]
    }),
    Prod($tau$,
    delim : $::=$,
    annot : $sans("Type")$,
    {
        Or[`int`][_entier_]
        Or[`&mut `$tau$][_référence mutable_]
        Or[`&`$tau$][_référence partagée_]
    }),
    Prod($bullet.stroked.o$,
    delim : $::=$,
    annot : $sans("Opérateur")$,
    {
        Or[$+$][]
        Or[$-$][]
        Or[$*$][]
        Or[$\/$][]
        Or[$%$][]
    }),
    Prod($ast.op.o$,
    delim : $::=$,
    annot : $sans("Comparateur")$,
    {
        Or[`<=`][]
        Or[`<`][]
        Or[`>=`][]
        Or[`>`][]
        Or[`==`][]
        Or[`!=`][]
    }),
)
Ce sous ensemble modélise la représentation intermédiaire du compilateur `rustc` (MIR) réduite aux expressions et instructions de base pour l'analyse des références.

#notice[
    L'expression $[z_1;z_2]$ représente formellement le non-déterminisme, ce qui correspond en Rust à un appel à `std::random::random()`.\
    Les boucles sont non-conventionnelles et correspondent à celle de la MIR, où $i in NN$ représente un identifieur unique correspondant informellement au niveau d'imbrication. Par exemple :
    ```rust
    loop(0) { // (L0)
        loop(1) {
            if (i % 2 == 0) {
                break 0 // (L1)
            } else {
                ()
            }
        }
    }
    ```
    ici, à la ligne `(L1)` on a `break(0)` qui correspond à la terminaison de la boucle `(L0)`.
]

#example[
    exemple de programme :
    ```rust
    storage_live(local6 : int);
    storage_live(a : int);
    storage_live(b : int);
    storage_live(c : &mut int);
    a = 0;
    b = 0;
    if ([-∞;+∞] != 0) {
        c = &mut a
    } else {
        c = &mut b
    };
    local6 = copy(*c) + 1;
    *c = move(local6);
    storage_dead(local6 : int);
    storage_dead(c);
    storage_dead(a);
    storage_dead(b)
    ```
    correspondant au programme suivant en Rust :
    ```rust
    let mut a = 0;
    let mut b = 0;
    let c = if std::random::random() {
        &mut a
    } else {
        &mut b
    };
    *c += 1;
    ```
]

== Typage

On présente ici le système de type de $lambda_"MIR"$, par induction structurelle sur les expressions. On se munit d'un jugement de type $Gamma : cal(V) arrow Tau$ (en notant $Tau$ l'ensemble des types).
#let rules = ()

#rules.push(prooftree(rule(
    label : [],
    name : [($T_0$)],
    [$Gamma, x : tau tack x : tau$],
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_1$)],
    [$Gamma tack z in ZZ : $`int`]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_2$)],
    [$Gamma tack [z_1 in ZZ union {-infinity};z_2 in ZZ union {+infinity}]$ : `int`]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_3$)],
    [$Gamma tack e_1 bullet.stroked.o e_2 :$ `int`],
    [$Gamma tack e_1 :$ `int`],
    [$Gamma tack e_2 :$ `int`]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_4$)],
    [$Gamma tack (*e) : tau$],
    [$Gamma tack e : $ `&mut` $tau$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_5$)],
    [$Gamma tack (*e) : tau$],
    [$Gamma tack e : $ `&`$tau$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($T_6$)],
    [$Gamma tack $`copy`$(e) : tau$],
    [$Gamma tack e : tau$]
)))

#let rule-set(rules, spacing: 3em) = {
  block(rules.map(box).join(h(spacing, weak: true)))
}
#align(center, rule-set(rules))

et pour les instructions, on ajoute les règles suivantes, en notant $Gamma, s tack $`ok` pour dire que $s$ est bien typé sous le contexte $Gamma$ :
#let rules = ()

#rules.push(prooftree(rule(
    label : [],
    name : [($S_0$)],
    [$Gamma tack $`if` $(e_1 ast.op.o e_2){s_1}$ `else` ${s_2}$ : `ok`],
    [$Gamma tack e_1$ : `int`],
    [$Gamma tack e_2$ : `int`],
    [$Gamma tack s_1$ : `ok`],
    [$Gamma tack s_2$ : `ok`],
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_1$)],
    [$Gamma, e_1 : #text[`int`] tack (e_1 = e_2)$ : `ok`],
    [$Gamma, e_1 : #text[`int`] tack e_2 : #text[`int`]$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_2$)],
    [$Gamma, v : tau tack (x =$ `move`$(v)) :$ `ok`],
    [$Gamma, v : tau tack x : tau$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_3$)],
    [$Gamma, x : tau tack (u=$ `&mut` $x$) : `ok`],
    [$Gamma, x : tau tack u : $ `&mut` $tau$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_4$)],
    [$Gamma, x : tau tack (u=$ `&`$x$) : `ok`],
    [$Gamma, x : tau tack u : $ `&`$tau$]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_5$)],
    [$Gamma tack $`loop`$(i in NN){s}$ : `ok`],
    [$Gamma tack s$ : `ok`],
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_6$)],
    [$Gamma tack $`storage_live`$(x : tau); s$ : `ok`],
    [$Gamma, x : tau tack s$ : `ok`]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_7$)],
    [$Gamma, x : tau tack $`storage_dead`$(x : tau); s$ : `ok`],
    [$Gamma tack s$ : `ok`]
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_8$)],
    [$Gamma tack $ `break`$(i in NN)$ : `ok`],
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_9$)],
    [$Gamma tack $ `()` : `ok`],
)))

#rules.push(prooftree(rule(
    label : [],
    name : [($S_10$)],
    [$Gamma tack s_1; s_2$ : `ok`],
    [$Gamma tack s_1$ : `ok`],
    [$Gamma tack s_2$ : `ok`]
)))

#let rule-set(rules, spacing: 3em) = {
  block(rules.map(box).join(h(spacing, weak: true)))
}
#align(center, rule-set(rules))

#notice[
    Ce système de type ne vérifie pas les emprunts. Ces derniers sont vérifiés dans une passe de compilation séparée après le typage appelée #emph[borrow checking].
]

= Sémantique transitionnelle des programmes

#definition[
    Un état $cal(S)$ d'un programme Rust consiste en une fonction des variables du programme $cal(V)$ vers les entiers mathématiques (scalaire) et les variables (références), i.e.:
    $ #eq_def($cal(S)$, $cal(V) arrow ZZ union cal(P)^tr$) $
    En notant $#eq_def($cal(P)^tr$, $cal(V) union {"INVALID", "UNINIT"}$)$
]

Cette définition ne modélise volontairement pas d'allocations dynamiques sur le tas, ce qui simplifie le domaine sémantique à l'étude.
Ces allocations seront ajoutées plus tard.

#definition[
    Notre sémantique concrète peut être séparée entre la sémantique concrète numérique (les variables de type `int`) et la sémantique concrète des références (les variables de type `&`$tau$, et `&mut` $tau$). On note le domaine concret numérique :
    $ (cal(D), subset.eq, union, inter, emptyset, cal(P)(cal(V) arrow ZZ)) #text[ où ] #eq_def($cal(D)$, $union.big_(S in cal(P)(cal(S))) {rho_(|S_#text[`int`]) | rho in S}$) $
    En notant pour tout $S in cal(P)(cal(S))$ :
    $ #eq_def($S_#text[`int`]$, ${x | x in S, x : #text[`int`]}$) $
]

#example[
    Dans l'exemple précédent, on aurait au début du programme :
    $ (a arrow "UNINIT", b arrow "UNINIT", c arrow "UNINIT") $
    Puis à la fin du programme avant les désallocations l'environnement suivant :
    $ (a arrow 0, b arrow 1, c arrow b) $
    si `std::random::random()` a été évalué à un scalaire supérieur à 0, et :
    $ (a arrow 1, b arrow 0, c arrow a) $
    sinon. Puis après les désallocations :
    $ (a arrow "INVALID", b arrow "INVALID", c arrow "INVALID") $
]

== Sémantique des expressions

#let esem(body) = {
    set text(red)
    [$EE [|$#text(black)[#body]$|]$]
}

La sémantique d'une expression $e$ est dénotée #esem($e$) $: cal(S) arrow cal(P)(ZZ) union cal(P)(cal(P^tr))$. Pour un état d'entrée donné,
l'expression est évaluée dans l'ensemble des valeurs de sorties possibles (à cause du non déterminisme). Une variable est évaluée
à l'aide de l'état d'entrée $sigma$. Si la variable n'est pas définie, on renvoie l'ensemble vide et on considère cet état comme une erreur.
On disjoint l'union entre les scalaires et les variables car on part du principe que le programme est bien typé, donc une expression a un type unique et ne peut pas s'évaluer en 
un ensemble de valeurs contenant à la fois des entiers et des références.
On a alors :
$ #eq_def($#esem($v in cal(V)$) sigma$, ${sigma(v)}$) $
$ #eq_def($#esem($z in ZZ$) sigma$, ${z}$) $
$ #eq_def($#esem($[z_1; z_2]$) sigma$, ${z in ZZ | z_1 <= z <= z_2}$) $
$ #eq_def($#esem($e_1 bullet.stroked.o e_2$) sigma$,$#esem($e_1$) sigma bullet.stroked.o #esem($e_2$) sigma$) $
Avec :
$ #eq_def($X bullet.stroked.o Y$, ${x bullet.stroked.o y | x in X, y in Y} forall bullet.stroked.o in {+, -, *}$) $
$ #eq_def($X \/ Y$, ${x \/ y | x in X, y in Y, y != 0} $) $
$ #eq_def($X % Y$, ${x % y | x in X, y in Y, y != 0} $) $
Puis pour les expressions liées aux références :
$ #eq_def($#esem($*v$) sigma$, $union.big_(u in sigma(v),\ u != "INVALID",\ u != "UNINIT") {sigma(u)}$) $
$ #eq_def($#esem([`copy`$(e)$]) sigma$, $#esem($e$) sigma$) $

#notice[
    le `move` est traité comme une instruction car il n'a une sémantique attribuée que pour l'affectation d'un `move`, il en va de même pour les emprunts mutables et partagés, les expressions ci-dessous sont donc invalides :
    #align(center)[
        $x =$ `move`$(v) + 1$\
        $x =$ `&mut` $v + 1$
    ]
]

== Sémantique des instructions

#let ssem(body) = {
    set text(red)
    [$SS [|$#text(black)[#body]$|]$]
}

A cause du non-déterminisme des expressions, on peut se retrouver avec une affectation qui transforme un état du programme en plusieurs. On note #ssem($s$) : $cal(S) arrow cal(P)(cal(S))$ la sémantique d'une instruction $s$. Pour faciliter leur composition, on définit une extension #ssem($s$) : $cal(P)(cal(S)) arrow cal(P)(cal(S))$.
La sémantique d'une instruction, étant donné l'ensemble des états possibles avant l'instruction, associe l'ensemble des états possibles après l'instruction. Pour $Sigma$ un ensemble d'états, on a alors :
$ #eq_def($#ssem([`storage_live`$(v : $`int`$)$]) Sigma$, ${sigma[v arrow z] | sigma in Sigma, z in ZZ}$) $
$ #eq_def($#ssem($x = e$) Sigma$, ${sigma[x arrow v] | sigma in Sigma, v in #esem($e$) sigma}$) $
$ #eq_def($#ssem([$x = $`move`$(v)$]) Sigma$, ${sigma[x arrow sigma(v), v arrow "UNINIT"] | sigma in Sigma}$) $
$ #eq_def($#ssem($s_1;s_2$)$, $#ssem($s_2$) compose #ssem($s_1$)$) $
$ #eq_def($#ssem([`storage_dead`$(v : $`int`$)$]) Sigma$, ${sigma[v arrow "INVALID", forall x in cal(V), #text[tq.] sigma(x)=v, x arrow "INVALID"] | sigma in Sigma}$) $

Pour les références, on ajoute :
$ #eq_def($#ssem([`storage_live`$(v : $`&`$tau)$]) Sigma$, ${sigma[v arrow "UNINIT"] | sigma in Sigma}$) $
$ #eq_def($#ssem([$*x = e$]) Sigma$, ${sigma[u arrow v] | sigma in Sigma, v in #esem($e$) sigma, u in #esem($x$) sigma, u != "INVALID", u != "UNINIT"}$) $
$ #eq_def($#ssem([`storage_dead`$(v : $`&`$tau)$]) Sigma$, ${sigma[v arrow "INVALID", forall x in cal(V), #text[tq.] sigma(x)=v, x arrow "INVALID"] | sigma in Sigma}$) $
$ #eq_def($#ssem([$x=$ `&` $v$])Sigma$, ${sigma[x arrow v] | sigma in Sigma}$) $
$ #eq_def($#ssem([$x=$ `&mut` $v$])Sigma$, ${sigma[x arrow v] | sigma in Sigma}$) $

=== Sémantique des instructions conditionnelles
#let filter(body) = {
    set text(red)
    [$CC [|$#text(black)[#body]$|]$]
}

Pour les instructions conditionnelles, on définit un opérateur de filtrage conditionnel $#filter($c$)$ :
$ #eq_def($#filter($e_1 ast.op.o e_2$)$, ${sigma in Sigma | exists v_1 in #esem($e_1$) sigma, exists v_2 in #esem($e_2$) sigma, v_1 ast.op.o v_2}$) $
On peut ensuite définir :
$ #eq_def($#ssem([`if`$(c){s_t}$`else`${s_f}$])$, $#ssem($s_t$) compose #filter($c$) union #ssem($s_f$) compose #filter($not c$)$) $

=== Sémantique des boucles

Pour les boucles, on itère sur le corps de la boucle à l'infini puis on garde les états qui ont quitté la boucle (i.e., qui ont croisé un `break` au label $i in NN$ correspondant à la boucle),
on doit donc d'abord définir un état concret $chevron.l Sigma, "out" chevron.r in cal(P)(cal(S)) times (NN arrow cal(P)(cal(S)))$, où pour $i in NN$, $"out"(i)$ correspond aux états collectés à la fin des `break`$(i)$, tel que :\
Pour tout $s in #text[`Instruction`], s != #text[`break`], s != #text[`loop`]$ :
$ #eq_def($#ssem($s$) chevron.l Sigma, "out" chevron.r$, $chevron.l #ssem($s$) Sigma, "out" chevron.r$) $
Puis `break`$(i in NN)$ déplace tous les états courants dans $"out"(i)$ :
$ #eq_def($#ssem([`break`$(i in NN)$]) chevron.l Sigma, "out" chevron.r$, $chevron.l emptyset, "out"[i arrow "out"(i) union Sigma] chevron.r$) $
Et à la fin d'une boucle `loop`$(i in NN)$, les états sortants sont les $"out"(i)$ :
$ #eq_def($#ssem([`loop`$(i in NN){s}$]) chevron.l Sigma,"out" chevron.r$, [`let` $chevron.l Sigma', "out"' chevron.r = $ lfp$(#ssem($s$)) chevron.l Sigma, "out" chevron.r$ `in` $chevron.l "out"'(i), "out"'[i arrow emptyset] chevron.r$])\
#text[avec :] #eq_def($"lfp"(#ssem($s$)) chevron.l Sigma, "out" chevron.r$, $lim_(n arrow infinity) F_n chevron.l Sigma, "out" chevron.r$),\
#text[où] #eq_def($F_n chevron.l Sigma, "out" chevron.r$, $cases(
    chevron.l Sigma comma "out" chevron.r "si" n = 0,
    #ssem($s$) (F_(n - 1) chevron.l Sigma comma "out" chevron.r) union F_(n-1) chevron.l Sigma comma "out" chevron.r "sinon"
)$) $

= Sémantique abstraite <numerical>

#let ssems(body) = {
    set text(red)
    [$SS^sharp [|$#text(black)[#body]$|]$]
}

#let ssemis(body) = {
    set text(red)
    [$SS_i^sharp [|$#text(black)[#body]$|]$]
}

#let esems(body) = {
    set text(red)
    [$EE^sharp [|$#text(black)[#body]$|]$]
}

#let filters(body) = {
    set text(red)
    [$CC^sharp [|$#text(black)[#body]$|]$]
}

On prend un domaine abstrait numérique $cal(D)^sharp$ muni de :
1. un ensemble $cal(D)^sharp$ de valeurs abstraites,
2. un ordre partiel muni d'un algorithme effectif $attach(subset.eq.sq, tr: sharp)$ sur $cal(D)^sharp$,
3. une fonction de concrétisation $gamma : cal(D)^sharp arrow cal(D)$,
4. un plus petit élément $bot^sharp in cal(D)^sharp$ et un plus grand élément $top^sharp in cal(D)^sharp$,
5. des abstractions effectives et *sûres* des conditions et des affectations arithmétiques :
$ #ssems($v = e$) : cal(D)^sharp arrow cal(D)^sharp $
$ #filters($e_1 ast.op.o e_2$) : cal(D)^sharp arrow cal(D)^sharp $
telles que :
$ forall sigma^sharp in cal(D)^sharp : (#ssem($v = e$) compose gamma)sigma^sharp subset.eq (gamma compose #ssems($v = e$))sigma^sharp $
$ forall sigma^sharp in cal(D)^sharp : (#filter($e_1 ast.op.o e_2$) compose gamma)sigma^sharp subset.eq (gamma compose #filters($e_1 ast.op.o e_2$))sigma^sharp $
6. des abstractions effectives et *sûres* de l'union ensembliste et de l'intersection :
$ union^sharp : cal(D)^sharp times cal(D)^sharp arrow cal(D)^sharp $
$ inter^sharp : cal(D)^sharp times cal(D)^sharp arrow cal(D)^sharp $
telles que :
$ forall sigma_1^sharp, sigma_2^sharp in cal(D)^sharp : gamma(sigma_1^sharp) union gamma(sigma_2^sharp) subset.eq gamma (sigma_1^sharp union^sharp sigma_2^sharp) $
$ forall sigma_1^sharp, sigma_2^sharp in cal(D)^sharp : gamma(sigma_1^sharp) inter gamma(sigma_2^sharp) subset.eq gamma (sigma_1^sharp inter^sharp sigma_2^sharp) $
7. un opérateur d'élargissement $nabla$.

A partir de ce domaine abstrait, on définit la sémantique abstraite des programmes ci-dessous.

== Sémantique abstraite des instructions

On peut définir la sémantique abstraite des instructions par induction avec quelques changements notables, pour $sigma^sharp in cal(D)^sharp$, $"out"^sharp in NN arrow cal(D)^sharp$, pour tout $s in #text[`Instruction`], s != #text[`break`], s != #text[`loop`]$ :
$ #eq_def($#ssems($s$) chevron.l sigma^sharp, "out"^sharp chevron.r$, $chevron.l #ssems($s$) sigma^sharp, "out"^sharp chevron.r$) $
Puis :
$ #eq_def($#ssems[`break`$(i in NN)$] chevron.l sigma^sharp, "out"^sharp chevron.r$, $chevron.l bot^sharp, "out"^sharp [i arrow "out"^sharp (i) union^sharp sigma^sharp] chevron.r$) $
$ #eq_def($#ssems([`loop`$(i in NN){s}$]) chevron.l sigma^sharp, "out"^sharp chevron.r$, [`let` $chevron.l sigma^sharp ', "out"^sharp ' chevron.r = $ lfp$(#ssems($s$)) chevron.l sigma^sharp, "out"^sharp chevron.r$ `in` $chevron.l "out"^sharp '(i), "out"^sharp '[i arrow bot^sharp] chevron.r$\
avec :
$ #eq_def($"lfp"(#ssems($s$)) chevron.l sigma^sharp, "out"^sharp chevron.r$, $lim_(n arrow infinity) F_n^sharp chevron.l sigma^sharp, "out"^sharp chevron.r$) $\
où $#eq_def($F_n^sharp chevron.l X^sharp, "out"^sharp chevron.r$, $cases(
    chevron.l X^sharp comma "out"^sharp chevron.r "si" n = 0,
    F_(n-1)^sharp chevron.l X^sharp comma "out"^sharp chevron.r nabla #ssems($s$) (F_(n - 1)^sharp chevron.l X^sharp comma "out"^sharp chevron.r) "sinon"
)$)$]) $
$ #eq_def($#ssems([`if`$(c){s_t}$`else`${s_f}$])$, $#ssems($s_t$) compose #filters($c$) union^sharp #ssems($s_f$) compose #filters($not c$)$) $

#theorem[
    $#ssems($p$)$ termine toujours et est *sûre* :
    $ forall p in frak(S), sigma^sharp in cal(D)^sharp : #ssem($p$) (gamma(sigma^sharp)) subset.eq gamma(#ssems($p$)sigma^sharp) $
    En notant $frak(S)$ l'ensemble des programmes (induits par la grammaire @grammar).
]

La définition de l'opérateur d'élargissement $nabla$ assure que la limite $F_n^sharp$ est toujours atteinte après un nombre fini d'itérations. Le résultat de l'analyse est *sûr* : c'est la composition d'abstractions sûres.

= Domaine abstrait des références

#let gal(ps1, ps2) = {
    let double-arrow(spacing: 0.6em) = math.stack(
      (arrow.l.long, arrow.r.long),
      dy: spacing,
      dir: ttb,
      align: center
    )

    [#ps1 $arrows.lr_alpha^gamma$ #ps2]
}

On aimerait désormais raisonner de manière *automatique* sur les références. Ces dernières sont intuitivement moins compliquées que les pointeurs du langage C du fait que les emplacements en mémoire sont indivisibles.
On a aussi l'information du #emph[borrow checker] modélisée en @borrowchk qui nous indique qu'une zone mémoire doit avoir au plus un seul emprunt mutable à la fois, qui est temporairement "responsable" de la zone.
Cette information induit une adaptation des sémantiques abstraite et concrète.

== Exemple motivateur <example>

On s'intéresse au programme suivant :
#set table(stroke: (x, y) => (
  left: if x > 0 { 0.10pt },
  top: if y > 0 { 0.8pt },
))
#align(center)[
    #table(
      columns: 2,
      align: center,
      fill: aqua.lighten(90%),
      table.header[Programme $lambda_"MIR"$][Programme Rust],
      [
        ```rust
        storage_live(a : int);
        storage_live(b : int);
        a = [0, 10];
        b = [0, 10];
        storage_live(ma : &mut int);
        storage_live(mb : &mut int);
        ma = &mut a;
        mb = &mut b;
        storage_live(mc : &mut int);
        if (*ma >= *mb) {
            mc = ma;
        } else {
            mc = mb;
        };
        *mc += 1;
        [...]
        ```
      ],
      [
        ```rust
        let a = std::random::random() % 10;
        let b = std::random::random() % 10;
        let ma = &mut a;
        let mb = &mut b;
        let mc = if *ma >= *mb {
            ma
        } else {
            mb
        };
        *mc += 1;
        [...]
        ```
      ]
    )
]

#notice[
    On choisit un emprunt selon les valeurs de $a$ et $b$ qui sont non déterministes, et on incrémente le déréférencement de cet emprunt.\
    On aimerait être capable de prouver que le programme vérifie la post-condition $a != b$.
]
La difficulté réside ici dans le choix de la zone mémoire au moment de l'exécution de :
#align(center, [
    ```rust
    *mc += 1;
    ```
])
Ce choix peut être entièrement non déterministe si l'on change le test `*ma >= *mb`, auquel cas pour rester sûr en utilisant le domaine des intervalles, on devra modifier l'état mémoire de manière à avoir :
$ sigma = (a arrow [0; 11], b arrow [0; 11]) $
Dans ce cas, l'invariant $a != b$ n'est plus prouvé. Et dans le cas où la condition d'emprunt est déterministe (comme sur cet exemple), on souhaiterait garder l'information que :
$ #text[`mc`] = cases(
    #text[`ma`] "si " #text[`*ma >= *mb`],
    #text[`mb`] "sinon"
) $
De cette manière, on tirerait une meilleure précision que sur un domaine classique de pointeurs du fait que les références Rust sont généralement plus strictes dans leur définition :
en effet, un pointeur en C peut pointer vers un nombre potentiellement très dense de variables, tandis qu'une référence Rust ne pointera jamais sur plus qu'un nombre statique prédéfini à la compilation de variables.\
Cela est dû à la sémantique de possession, vérifiée par le #emph[borrow checker], où par exemple :
#align(center)[
    #table(
      columns: 1,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut a = [0;4096]; // définition d'un tableau de taille 4096
        let b = &mut a[0];
        let c = &mut a[1];
        [...] // opérations sur b
        ```
      ]
    )
]
ne compile pas, en affichant l'erreur suivante :
#align(center)[
    #table(
      columns: 1,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```bash
        error[E0499]: cannot borrow `a[_]` as mutable more than once at a time
        ```
      ]
    )
]
Ces emprunts sont un problème uniquement du fait qu'ils soient mutables.
Dans le cas d'une référence partagée, on peut réaliser autant d'emprunts que l'on veut même si la philosophie générale de la programmation en Rust encourage un faible nombre de références partagées.
Cette information nous permet de créer un modèle plus précis pour modéliser les références, mais aussi vérifier l'absence de bugs du compilateur en s'intéressant à sa sémantique d'emprunts formalisée @borrowchk.

== Domaine de base $cal(E)^sharp$

=== Etat mémoire abstrait $cal(E)$

#definition[
On définit le treillis $(cal(P)(cal(E)), prec.curly.eq, union)$ avec :
$ #eq_def($cal(E)$, $union.big_(C subset.eq cal(V)) {chevron.l C, rho chevron.r | rho in C arrow ZZ union cal(P)^tr}$) $ 
Avec l'ordre partiel suivant, pour $X, X' in cal(P)(cal(E))$ :
$ X prec.curly.eq X' arrow.l.r.double.long ^ Delta forall chevron.l C, rho chevron.r in X, exists chevron.l C', rho' chevron.r in X' : (C' subset.eq C) and (rho' = rho_(|C')) $
où $rho_(|C')$ dénote la restriction de $rho$ à $C'$, et $rho$ représente un environnement scalaire.\
Cet ensemble définit un état mémoire abstrait.
]

Cette sémantique abstraite est inspirée par l'analyse de portabilité #cite(<portability>) de l'analyseur Mopsa.

#example[
    Dans ce programme :
    ```rust
    storage_live(a : int);
    storage_live(b : int);
    storage_live(c : &mut int);
    a = 0;
    b = 1;
    if ([0;10] == 0) {
        c = &mut a
    } else {
        c = &mut b
    }
    ```
    On a :
    $ cal(R)={chevron.l {a, b, c}, rho_1 chevron.r, chevron.l {a, b, c}, rho_2 chevron.r} $
    Avec $rho_1[c arrow a, a arrow 0, b arrow 1], rho_2[c arrow b, a arrow 0, b arrow 1]$.
]

Une propriété abstraite $X in cal(P)(cal(E))$ représente l'ensemble concret d'états $gamma_cal(V)(X) in cal(P)(cal(V) arrow ZZ union cal(P)^tr)$ :
$ gamma_cal(V)(X) = {mu : cal(V) arrow ZZ union cal(P)^tr | exists chevron.l C, rho chevron.r in X : mu_(|C) = rho} $
La suppression de référence est toujours *sûre* : elle dénote une perte d'information.
Il est aussi possible d'ajouter des nouvelles références simplement : l'ajout d'une nouvelle référence initialisée à $top$ n'a pas d'effet de bord sur le reste de l'environnement et reste donc sûr.

=== Sémantique abstraite du #emph[Borrow Checker] <borrowchk>

Le #emph[borrow checker] a vérifié à la compilation jusqu'à la MIR que chaque espace mémoire a un unique propriétaire, qui est le seul à pouvoir éventuellement le modifier.
Une analyse dynamique des emprunts a été formalisée par le modèle de #emph[Stacked Borrows] #cite(<stacked>) dont la sémantique qui suit est inspirée.
Formellement, on ajoute $psi : cal(V) arrow "List"(I_cal(V))$ à l'état abstrait, avec :
$ #eq_def($I_cal(V)$, [${"unique"(v), v in cal(V)} union {"shared"(X), X subset.eq cal(V)}$]) $
$ #eq_def($"List"(I)$, [Nil | Cons($t$, $q$)]), t in I, q in "List"(I) $
Où, pour $v in cal(V)$, $psi(x) = "Cons"("unique"(v), q)$ représente l'appartenance de l'espace mémoire correspondant à $x$ par $v$, et $psi(x)="Cons"("shared"({v}), q)$ représente informellement un emprunt en lecture seule.
On appelle $psi(x)$ la pile d'emprunts correspondant à l'espace mémoire $x$.
Par exemple :
#align(center)[
    #table(
      columns: 1,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut a = 0;  // (L1)
        let b = &mut a; // (L2)
        let c = &mut b; // (L3)
        let d = &c;     // (L4)
        ```
      ]
    )
]
après (L4), on aura : 
$ psi(a)="Cons"("shared"(d), "Cons"("unique"(c), "Cons"("unique"(b), "Cons"("unique"(a), "Nil")))) $
que l'on note dans la suite par abus $psi(a)=["shared"({d}), "unique"(c), "unique"(b), "unique"(a)]$. On définit aussi par induction, pour $x, v in cal(V)$, les opérateurs :
$ x in psi(v) arrow.l.r.double.long ^ Delta (psi(v) = "Cons"(x, q)) or ("let" "Cons"(t, q) = psi(v) "in" x in q) $
$ #eq_def($"until"_"mut" (x, psi(v))$, $cases(
    "until"_"mut" (x, q) "si" psi(v) = "Cons"(t, q) comma t != "unique"(x),
    psi(v) "si" psi(v) = "Cons"("unique"(x), q),
    "Nil" "si" psi(v) = "Nil"
)$) $
$ #eq_def($"until"_"shr" (x, psi(v))$, $cases(
    psi(v) "si" psi(v) = "Cons"("shared"(X), q) comma x in X,
    "Nil" "si" psi(v) = "Nil",
    "until"_"shr" (x, q) "avec" psi(v) = "Cons"(t, q) "sinon"
)$) $
Les opérateurs until vont informellement supprimer tous les emprunts se situant avant $x$ dans la pile d'emprunts $psi(v)$, si $x$ appartient à cette pile. Avec la sémantique transitionnelle suivante, pour l'état concret $chevron.l C, psi, rho chevron.r$ :
$ #eq_def($#ssem([`storage_live`$(x)$])chevron.l C, psi, rho chevron.r$, ${chevron.l C, psi[x arrow ["unique"(x)]], rho chevron.r}$) $
Par défaut, $x in cal(V)$ est le seul alias à avoir des droits de lecture et d'écriture sur son espace mémoire. Puis les opérations d'emprunt mutable et partagé placent sur la pile d'emprunts de l'espace mémoire sous-jacent la nouvelle référence :
$ #eq_def($#ssem([$t = \&"mut" x$])chevron.l C, psi, rho chevron.r$, ${chevron.l C, psi[x arrow "Cons"("unique"(t), "until"_"mut" (x, psi(x)))], rho chevron.r}$) $
$ #eq_def($#ssem[$x = $`&`$v$] chevron.l C, psi, rho chevron.r$, ${chevron.l C, psi[x arrow cases(
    "Cons"("shared"({x} union X), q),
    "si" "until"_"shr" (v, psi(v))="Cons"("shared"(X), q),
    "Cons"("shared"({x}), psi(v)) "sinon"
)], rho chevron.r}$) $
Ensuite, si $x : #text[`&mut` ]tau$ est déréférencé, une occurence unique$(x)$ doit se trouver sur la pile d'emprunts correspondant à l'espace mémoire vers lequel il pointe :
$ #eq_def($#esem($*x$)chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"mut" (x, psi(rho(x)))] comma rho chevron.r} "si" "unique"(x) in psi(rho(x)),
    emptyset "sinon"
)$) $
On invalide alors tous les emprunts de la pile situés au dessus de unique$(x)$, qui ne peuvent désormais plus être utilisés. Par exemple :
#align(center)[
    #table(
      columns: 1,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut a = 0;  // (L1)
        let b = &mut a; // (L2)
        let c = &mut a; // (L3)
        *c += 4;        // (L4)
        ```
      ]
    )
]
Ce code sera validé par le #emph[borrow checker] uniquement dans le cas où $c$ n'est plus utilisé après l'usage de $b$ (L4). Au moment de (L3), on aura $psi(a)=["unique"(c), "unique"(b), "unique"(a)]$, puis après l'usage de l'emprunt $b$ (L4), $psi(a)=["unique"(b), "unique"(a)]$.\
Si $x : #text[`&`]tau$, on invalide les emprunts uniques qui ont une précédence sur $x$ dans la pile d'emprunts, i.e. les unique$(t)$, $t != x$ et shared$(X)$, $x in.not X$, d'où :
$ #eq_def($#esem($*x$) chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"shr" (x, psi(rho(x)))] comma rho chevron.r},
    "si" exists X subset.eq cal(V) comma "shared"({x} union X) in psi(rho(x)),
    emptyset "sinon"
)$) $
On peut tout de même garder tous les emprunts partagés qui ont été fait au même état mémoire que lors de l'emprunt partagé de $x$. Par exemple :
#align(center)[
    #table(
      columns: 2,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut a = 0;   // (L1)
        let b = &mut a;  // (L2)
        let c = &b;      // (L3)
        let d = &b;      // (L4)
        let e = &mut *b; // (L5)
        ```
      ],
      [
        $psi(a) = ["unique"(a)]$\
        $psi(a) = ["unique"(b), "unique"(a)]$\
        $psi(a) = ["shared"({c}), "unique"(b), "unique"(a)]$\
        $psi(a) = ["shared"({c, d}), "unique"(b), "unique"(a)]$\
        $psi(a) = ["unique"(e), "unique"(b), "unique"(a)]$
      ]
    )
]
$ #eq_def($#ssem($*x = e$)chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"mut" (x, psi(rho(x)))] comma rho chevron.r} "si" "unique"(x) in psi(rho(x)),
    emptyset "sinon"
)$) $
De même, le déréférencement d'un emprunt mutable est considéré comme un usage, ainsi $#ssem($*x = e$)$ a le même effet sur $psi$ que $#esem($*x$)$, et il en est de même pour un assignement de $x : tau$ :
$ #eq_def($#ssem($x = e$)chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"mut" (x, psi(rho(x)))] comma rho chevron.r} "si" "unique"(x) in psi(rho(x)),
    emptyset "sinon"
)$) $
L'instruction `move` va effectuer une modification en place de la pile d'emprunt pour informellement renommer l'occurence de $v$ en $x$, tout en prenant en compte que `move`$(v)$ constitue un usage de $v$ :
$ #eq_def($#ssem([$x =$`move`$(v)$])chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[v arrow "Cons"("unique"(x) comma q)] comma rho chevron.r},
    "si" v : tau comma v in psi(v) comma "until"_"mut" (v, psi(v)) = "Cons"("unique"(v), q),
    {chevron.l C comma psi[rho(v) arrow "Cons"("unique"(x), q)] comma rho chevron.r},
    "si" v : #text[`&mut` ]tau comma v in psi(rho(v)) comma "until"_"mut" (v, psi(rho(v))) = "Cons"("unique"(v), q),
    {chevron.l C comma psi[rho(v) arrow "Cons"("shared"({x}, X), q)] comma rho chevron.r},
    "si" v : #text[`&`]tau comma v in psi(rho(v)) comma "until"_"shr" (v, psi(rho(v))) = "Cons"("shared"({v} union X), q),
    emptyset "sinon"
)$) $
Et enfin, lorsqu'on enlève $x : tau$ de l'environnement, $psi$ sera mis à jour pour supprimer la pile d'emprunts correspondant à $x$ et en invalidant tous les éléments de la pile d'emprunts :
$ #eq_def($#ssem([`storage_dead`$(x)$])chevron.l C, psi, rho chevron.r$, $chevron.l C, psi[x arrow bot], rho[v arrow bot, forall v in psi(x)] chevron.r$) $

=== Définition de $cal(E)^sharp$

#definition[
    De là, on peut définir la sémantique concrète :
    $ #eq_def($cal(E)^sharp$, $union.big_(C subset.eq cal(V)) {chevron.l C, R chevron.r | R in cal(P)(C arrow ZZ union cal(P)^tr)}$) $
    que l'on munit aussi d'un ordre partiel :
    $ chevron.l C, R chevron.r prec.curly.eq^sharp chevron.l C', R' chevron.r arrow.l.r.double.long ^ Delta C' subset.eq C and {rho_(|C') | rho in R} subset.eq R' $
    formant aussi un treillis muni de l'union ensembliste paire-à-paire définie comme suit :
    $ #eq_def($chevron.l C, R chevron.r union^sharp chevron.l C', R' chevron.r$, $chevron.l C union C', R union R' chevron.r$)  $
]

On va construire une abstraction $gamma$ et une concrétisation $alpha$ :
$ #eq_def($alpha(X)$, $chevron.l #overline[C], { rho_(|#overline[C]) | chevron.l C, rho chevron.r in X } chevron.r$), #eq_def($#overline[C]$, $inter.big_(chevron.l C, rho chevron.r in X) {C}$) $
$ #eq_def($gamma chevron.l C, R chevron.r$, ${chevron.l C, rho chevron.r | rho in R}$) $
#theorem[
    On démontre qu'on a une correspondance Galoisienne entre $cal(E)$ et $cal(E)^sharp$ :
    $ #gal($(cal(P)(cal(E)), prec.curly.eq)$, $(cal(E)^sharp, prec.curly.eq^sharp)$) $
]
Cependant, cette sémantique n'est pas calculable car elle est très proche du concret, ce qui motive la suite : pour la rendre calculable on va séparer l'abstraction des variables numériques de celle des références. De cette manière, on pourra abstraire les variables numériques en le domaine abstrait $cal(D)^sharp$ @numerical, puis garder notre abstraction des références à part.
#definition[
    On définit la sémantique abstraite calculable :
    $ #eq_def($cal(E)^sharp_"cal"$, $union.big_(C subset.eq cal(V)){chevron.l C, d^sharp, rho^sharp chevron.r | rho^sharp in C_(cal(P)^tr) arrow cal(P)(cal(P)^tr), d^sharp in cal(D)^sharp (C_#text[`int`])}$) $
    Avec :
    $ #eq_def($C_#text[`int`]$, ${c in C | c : #text[`int`]}$) $
    $ #eq_def($C_(cal(P)^tr)$, ${c in C | c : #text[`&`]tau or c : #text[`&mut` ]tau}$) $
    et $cal(D)^sharp$ un domaine numérique abstrait.
]
Ce domaine donne une approximation de base des références qui est sûre et calculable, nous indiquant par exemple que dans @example, on aura :
$ #text[`mc`] arrow.long^"points to" {#text[`a`], #text[`b`]} $
mais n'est pas assez précis pour nous indiquer que $c$ pointera vers $a$ seulement sous certaines conditions liées à l'environnement. C'est ce qui motive le rafinement de notre abstraction de base $cal(E)^sharp$.

== Raffinement $cal(E)^sharp.double$

=== Raffinement $cal(E)^flat$ de l'état mémoire

#definition[
    Si on note :
    $ #eq_def($cal(C)^"ond"$, $cal(P)(#text[`cond`])$) $
    en notant `cond` l'ensemble des conditions induit de la grammaire @grammar, et que l'on munit $cal(C)^"ond"$ d'un ordre partiel pour $c, c' in cal(C)^"ond"$ :
    $ c subset.eq.sq c' arrow.l.r.double.long ^ Delta c' subset.eq c $
    et d'une union :
    $ #eq_def($c union.sq c'$, $c inter c'$) $
    $(cal(C)^"ond", subset.eq.sq, union.sq)$ forme un treillis qui définit un état abstrait des hypothèses.
]
Intuitivement, l'ordre $subset.eq.sq$ indique qu'un état abstrait ayant plus d'hypothèses sera plus précis.

#example[
    Si on prend le programme suivant :
    ```rust
    if (*a >= *b) { if (*c <= *d) {
        x = 2 // (L2)
    } }
    ```
    On aura $c in cal(C)^"ond" = {(#text[`*a >= *b`]), (#text[`*c <= *d`])}$ au moment de $("L2")$ dont la conjonction correspond bien aux hypothèses faites dans ce chemin d'exécution.
]

A partir de cet état abstrait des hypothèses, on aimerait garder l'information des hypothèses associées aux emprunts,
de manière à avoir plus de précision sur quel emprunt correspond à quel hypothèse, comme dans le cas de @example, où l'on voudrait garder :
$ #text[`mc`] arrow {(#text[`a`], #text[`*ma >= *mb`]), (#text[`b`], #text[`*ma < *mb`])} $
Donc informellement, savoir que `mc` pointe sur `a` si `*ma >= *mb`, et pointe sur `b` si `*ma < *mb`.

#definition[
    On définit l'état mémoire concret instrumenté $(cal(P)(cal(E)^flat), subset.eq, union)$ avec :
    $ #eq_def($cal(E)^flat$, $union.big_(C subset.eq cal(V)) {chevron.l C, rho chevron.r | rho in C arrow ZZ union (cal(P)^tr times cal(C)^"ond") }$) $
]
Cet état se souvient, avec chaque environnement, des contraintes accumulées lors de l'exécution jusqu'à ce point.

=== Abstraction $cal(E)^sharp.double$ de l'état mémoire

#definition[
    On raffine notre abstraction $cal(E)^sharp$ en $(cal(E)^sharp.double, subset.eq, union)$ avec :
    $ #eq_def($cal(E)^sharp.double$, $union.big_(C subset.eq cal(V)) {chevron.l C, d^sharp, rho^sharp chevron.r | rho^sharp in cal(P)_"finite" ((C_(cal(P)^tr) arrow cal(P)(cal(P)^tr)) times cal(C)^"ond"), d^sharp in cal(D)^sharp (C_#text[`int`])}$) $ 
]
Ce modèle est inspiré de la modélisation des références induite dans le modèle de #emph[RustBelt] #cite(<rustbelt>).
Informellement, $rho(v) in cal(P)(cal(P)^tr times cal(C)^"ond")$ #footnote[On note par abus $rho(v) = union.big_(rho_i in rho^sharp)rho_i (v) in cal(P)(cal(P)^tr times cal(C)^"ond")$] représente une surapproximation des valeurs vers lesquelles $v in cal(V)_(\&tau)$ peut pointer sous condition, ie. $(x, c) in rho(v)$ indique :
$ v arrow.long^(#text[`assume`]\(c\)) x $
Par exemple, dans @example, on aurait donc :
$ #text[`mc`] arrow.long^(#text[`assume`$($`*a>=*b`$)$]) #text[`a`]\
#text[`mc`] arrow.long^(#text[`assume`$($`*a<*b`$)$]) #text[`b`] $
Cette abstraction nous permet de retenir plus d'informations sur l'état mémoire, tout en restant sûr et calculable. On en déduit une sémantique transitionnelle pour l'état abstrait $chevron.l C, d^sharp, rho^sharp chevron.r$, avec $x : $ `&mut` $tau$, $x : $ `&`$tau$ :
$ #eq_def($#ssems[`storage_live`$(x)$]chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow top], c) | (rho, c) in rho^sharp} chevron.r$) $
$ #eq_def($#ssems[`storage_dead`$(x)$]chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow bot], c) | (rho, c) in rho^sharp} chevron.r$) $
$ #eq_def($#ssems[$t = $`&mut` $x$]chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[t arrow {x}], c) | (rho, c) in rho^sharp} chevron.r$) $
$ #eq_def($#ssems[$t = $`&`$x$]chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[t arrow {x}], c) | (rho, c) in rho^sharp} chevron.r$) $
$ #eq_def($#ssems[$x = $`move`$(v)$]chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow rho(v), v arrow {"INVALID"}], c) | (rho, c) in rho^sharp} chevron.r$) $
Pour le `move`, on prend soin d'invalider $v$ après la transmission des permissions à $x$.
$ #eq_def($#ssems[$"if"(c) {s_1} "else" {s_2}$]chevron.l C, d^sharp, rho^sharp chevron.r$, [\
    `let` $chevron.l C_1, d^sharp_1, rho^sharp_1 chevron.r = (#ssems($s_1$) compose #filters($c$)) chevron.l C, d^sharp, rho^sharp chevron.r$ `in`\
    `let` $chevron.l C_2, d^sharp_2, rho^sharp_2 chevron.r = (#ssems($s_2$) compose #filters($not c$)) chevron.l C, d^sharp, rho^sharp chevron.r$ `in`\
    $chevron.l C_1 union C_2, d_1^sharp union^sharp d_2^sharp, {(rho, "cond" union {c}) | (rho, "cond") in rho^sharp_1} union {(rho, "cond" union {not c}) | (rho, "cond") in rho^sharp_2} chevron.r$]) $
On accumule dans chaque sous environnement les conditions correspondant aux branches d'exécution prises.
Et enfin, dans le cas où $x : $ `&mut` $tau$ :
$ #eq_def($#ssems($*x = e$)chevron.l C, d^sharp, rho^sharp chevron.r$, [$union.big_((rho, c) in rho^sharp) (union.big_(v in rho(x)) (#ssems($v = e$) compose #filters($c$)) chevron.l C, d^sharp, {rho} chevron.r)$]) $
informellement, dans chaque environnement $(rho, c)$, on effectue l'assignement sous la condition $c$ des valeurs possibles vers lesquelles $x$ pointe.

= Propriétés d'intérêt particulières au Rust

Comme vu précédemment (@borrowchk), le #emph[borrow checker] nous assure que seulement une variable a la propriété d'un espace mémoire. Afin de gagner en expressivité, on autorise des transferts temporaires et définitifs d'appartenance. Ces transferts sont modélisés en pratique par :
$ x = #text[`move`]\(v\)\
x = #text[`&mut`] v $
qui sont deux composants essentiels du langage. Seule la variable ayant l'appartenance (temporairement ou définitivement) de l'espace mémoire est en capacité de l'utiliser de manière mutable. Par exemple :
#align(center)[
    #table(
      columns: 2,
      align: center,
      fill: aqua.lighten(90%),
      table.header[Programme $lambda_"MIR"$][Programme Rust],
      [
        ```rust
        storage_live(x : int);
        storage_live(t : &mut int);
        x = 4;
        t = &mut x;
        x = 5; // (L5)
        [...] // usage de t
        ```
      ],
      [
        ```rust
        let mut x = 4;
        let t = &mut x;
        x = 5; // (L5)
        [...] // usage de t
        ```
      ]
    )
]
Ce programme n'est pas valide car au moment de $("L5")$, $t$ est le garant de l'espace mémoire correspondant à $x$. En pratique, le compilateur vérifie au moment du #emph[borrow checking] ces emprunts et ne compilera effectivement pas le programme si ils se trouvent être invalides.\
#definition[
    Pour vérifier que le #emph[borrow checking] est en effet correct, on ajoute à l'état abstrait $chevron.l C, d^sharp, rho^sharp chevron.r$ une dernière composante $psi^sharp : C_#text[`int`] arrow cal(P)("List"(I_C))$ qui représente une abstraction de $psi$ @borrowchk. On a alors :
    $ #eq_def($cal(E)^sharp.double_"chk"$, $union.big_(C subset.eq cal(V)) {chevron.l C, d^sharp, rho^sharp, psi^sharp chevron.r | chevron.l C, d^sharp, rho^sharp chevron.r in cal(E)^sharp.double_C, psi^sharp in cal(P)_"finite" (C_#text[`int`] arrow cal(P)("List"(I_C)))}$) $
]

= #emph[Raw pointeurs]

Pour garder une expréssivité similaire au C, dans des cas où la discipline imposée par le #emph[borrow checker] s'avère trop stricte, une option peut être d'utiliser des #emph[raw pointeurs]. Les #emph[raw pointeurs] du Rust sont similaires aux pointeurs du C,
ils ne sont pas vérifiés par le compilateur et n'ont pas de restrictions d'alias. Par exemple :
#align(center)[
    #table(
      columns: 1,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut x = 0;                    // (L1)
        let ptr1 = &mut x as *mut i32;    // (L2)
        let ptr2 = ptr1;                  // (L3)
        unsafe { *ptr1 = 1; }             // (L4)
        unsafe { println!("{}", *ptr2); } // (L5) affiche 1
        ```
      ]
    )
]
A la ligne (L2), on va convertir le type `&mut i32` en `*mut i32`. Ce #emph[raw pointeur] peut ensuite être dupliqué comme à la ligne (L3).
La création de #emph[raw pointeurs] fait partie du langage sûr, mais lorsque l'on veut accéder au contenu du #emph[raw pointeur] en le déréférençant pour y lire ou y écrire,
l'opération est marquée `unsafe`, indiquant que c'est à l'appréciation de l'utilisateur de s'assurer de la sûreté de ses opérations.
Informellement, pour s'assurer de leur sûreté le programmeur doit vérifier que l'espace mémoire pointé est valide au moment du déréférencement.

== Grammaire et typage

On ajoute à la grammaire les opérations de conversion de type ainsi que les types associés aux #emph[raw pointeurs] :
#bnf(
    Prod("s",
    delim : "+=",
    annot: $sans("Instruction")$,
    {
        Or[$v =$ $v$ as `*mut` $tau$][_conversion mutable_]
        Or[$v =$ $v$ as `*const` $tau$][_conversion immuable_]
    }),
    Prod($tau$,
    delim : "+=",
    annot: $sans("Type")$,
    {
        Or[`*const` $tau$][_raw pointeur immuable_]
        Or[`*mut` $tau$][_raw pointeur mutable_]
    })
)
Et on se munit à nouveau d'un jugement de type $Gamma : cal(V) arrow Tau$ :
#let rules = ()

#rules.push(prooftree(rule(
    label : [],
    name : [($S_11$)],
    [$Gamma, x : #text[`&mut`] tau tack (v = x #text[as `*mut`] tau) : #text[`ok`]$],
    [$Gamma, x : #text[`&mut`] tau tack v : #text[`*mut`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($S_12$)],
    [$Gamma, x : #text[`&`] tau tack (v = x #text[as `*const`] tau) : #text[`ok`]$],
    [$Gamma, x : #text[`&`] tau tack v : #text[`*const`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($S_13$)],
    [$Gamma, v : tau tack (#text[`*`] x = v) : #text[`ok`]$],
    [$Gamma, v : tau tack x : #text[`*mut`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($S_1$)],
    [$Gamma, e_1 : #text[`*mut`] tau tack (e_1 = e_2)$ : `ok`],
    [$Gamma, e_1 : #text[`*mut`] tau tack e_2 : #text[`*mut`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($S_1$)],
    [$Gamma, e_1 : #text[`*const`] tau tack (e_1 = e_2)$ : `ok`],
    [$Gamma, e_1 : #text[`*const`] tau tack e_2 : #text[`*const`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($T_7$)],
    [$Gamma tack (#text[`*`] x) : tau$],
    [$Gamma tack x : #text[`*const`] tau$]
)))
#rules.push(prooftree(rule(
    label : [],
    name : [($T_8$)],
    [$Gamma tack (#text[`*`] x) : tau$],
    [$Gamma tack x : #text[`*mut`] tau$]
)))
#let rule-set(rules, spacing: 3em) = {
  block(rules.map(box).join(h(spacing, weak: true)))
}
#align(center, rule-set(rules))
Ainsi, on garde le même opérateur \`$*$\` pour le déréférencement. Simplement,
sa sémantique se verra transformée dans le cas des #emph[raw pointeurs] ci-dessous.
On remarque aussi que les #emph[raw pointeurs] ont une sémantique associée à l'assignation contrairement aux références,
car les alias sont autorisés.

== Sémantique transitionnelle des programmes

On garde le même état d'un programme Rust :
$ #eq_def($cal(S)$, $cal(V) arrow ZZ union cal(P)^tr$) $
car cet état mémoire englobe déjà les valeurs d'un pointeur, qui sont les mêmes qu'une référence.
On en déduit une sémantique transitionnelle pour un ensemble d'états $Sigma$ :
$ #eq_def($#ssem([`storage_live`$(v : $`*mut` $tau)$])Sigma$, ${sigma[v arrow "UNINIT"] | sigma in Sigma}$) $
$ #eq_def($#ssem([`storage_live`$(v : $`*const` $tau)$])Sigma$, ${sigma[v arrow "UNINIT"] | sigma in Sigma}$) $
$ #eq_def($#ssem([`storage_dead`$(v : $`*mut` $tau)$])Sigma$, ${sigma[v arrow "INVALID", forall x in cal(V), #text[tq. ]sigma(x)=v, x arrow "INVALID"] | sigma in Sigma}$) $
$ #eq_def($#ssem([`storage_dead`$(v : $`*const` $tau)$])Sigma$, ${sigma[v arrow "INVALID", forall x in cal(V), #text[tq. ]sigma(x)=v, x arrow "INVALID"] | sigma in Sigma}$) $
Les #emph[raw pointeurs] agissent donc à l'allocation et la désallocation comme des références.
Pour $x, v : #text[`*const` ]tau$ ou $#text[`*mut`] tau$ :
$ #eq_def($#ssem([$x = v$])Sigma$, ${sigma[x arrow u] | u in #esem($v$)sigma, sigma in Sigma}$) $
On autorise la création d'alias par l'assignation directe, contrairement aux références où le seul moyen de transmettre les valeurs
d'une référence à une autre s'opère par l'instruction `move`, qui *invalide* l'ancienne variable.
Puis pour $y : #text[`*mut` ]tau$ :
$ #eq_def($#ssem([$*y = e$])Sigma$, ${sigma[x arrow v] | x in #esem($*y$)sigma, v in #esem($e$)sigma, sigma in Sigma}$) $
Enfin, pour $x : #text[`*const` ]tau, x : #text[`*mut` ]tau$ et $sigma$ état d'entrée :
$ #eq_def($#esem($*x$)sigma$, $union.big_(u in sigma(x)\ u != "INVALID"\ u != "UNINIT") {sigma(u)}$) $

== Sémantique abstraite du #emph[Borrow Checker] pour les #emph[raw pointeurs]

On aimerait un modèle permettant de s'assurer que les garanties mémoires du Rust restent inviolées en dehors du cadre de l'exécution de blocs marqués `unsafe`.
Pour cela, il nous faut l'information d'un emprunt par un #emph[raw pointeur] dans la pile d'emprunt correspondant à l'espace mémoire.
On ajoute donc à $I_cal(V)$ un objet sharedRW qui modélise l'emprunt par des #emph[raw pointeurs], i.e. :
$ #eq_def($I_cal(V)$, $I_cal(V) union {"sharedRW"}$) $
qui modélise informellement l'information d'un emprunt par un #emph[raw pointeur].
On définit un opérateur $"until"_"raw"$ pour $v in cal(V)$ de la même manière que dans @borrowchk :
$ #eq_def($"until"_"raw" (psi(v))$, $cases(
    psi(v) "si" psi(v) = "Cons"("sharedRW", q),
    "until"_"raw" (q) "si" psi(v) = "Cons"(t, q) comma t != "sharedRW",
    "Nil" "si" psi(v) = "Nil"
)$) $
Avec la sémantique transitionnelle suivante pour l'état concret $chevron.l C, psi, rho chevron.r$ :
$ #eq_def($#ssem[$x = v$ as `*mut` $tau$]chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(v) arrow "Cons"("sharedRW", "until"_"mut" (v, psi(rho(v))))] comma rho chevron.r},
    "si" "unique"(v) in psi(rho(v)),
    emptyset "sinon"
)$) $
$ #eq_def($#ssem[$x = v$ as `*const` $tau$]chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(v) arrow "Cons"("sharedRW", "until"_"shr" (v, psi(rho(v))))] comma rho chevron.r},
    "si" exists X subset.eq cal(V) comma "shared"({v} union X) in psi(rho(v)),
    emptyset "sinon"
)$) $
Ainsi, la création d'un #emph[raw pointeur] $x$ est considérée comme un usage de la référence $v$ qu'il a transtypée. Puis, pour $x : #text[`*mut` ]tau, #text[`*const` ]tau$ :
$ #eq_def($#esem($*x$)chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"raw" (psi(rho(x)))] comma rho chevron.r} "si" "sharedRW" in psi(rho(x)),
    emptyset "sinon"
)$) $
$ #eq_def($#ssem($*x = e$)chevron.l C, psi, rho chevron.r$, $cases(
    {chevron.l C comma psi[rho(x) arrow "until"_"raw" (psi(rho(x)))] comma rho chevron.r} "si" "sharedRW" in psi(rho(x)),
    emptyset "sinon"
)$) $
Par exemple :
#align(center)[
    #table(
      columns: 2,
      align: center,
      fill: aqua.lighten(90%),
      [
        ```rust
        let mut a = 0;               // (L1)
        let b = &mut a;              // (L2)
        let c = &mut *b as *mut i32; // (L3)
        *b = 4;                      // (L4)
        unsafe { *c += 2; }          // (L5)
        ```
      ],
      [
        $psi(a) = ["unique"(a)]$\
        $psi(a) = ["unique"(b), "unique"(a)]$\
        $psi(a) = ["sharedRW", "unique"(b), "unique"(a)]$\
        $psi(a) = ["unique"(b), "unique"(a)]$\
        $psi(a) = emptyset$
      ]
    )
]
On aura $psi(a)=emptyset$ à (L5) bien que un programme Rust accepte ce code
car il brise l'invariant d'un environnement à un seul possesseur à la fois pour $a$ :
ici $b$ et $c$ sont possesseurs en simultané car ils sont utilisés à la suite après leur définition,
qui est contraire à la philosophie du langage.

// == Sémantique abstraite des #emph[raw pointeurs]
// 
// L'état mémoire $cal(E)$ inchangé convient à l'analyse des #emph[raw pointeurs] car leur manipulation ne diffère pas de
// celle des références en dehors de l'analyse du #emph[borrow checker]. Simplement, l'abstraction des #emph[raw pointeurs] nécessitera la sémantique abstraite calculable $cal(E)^sharp_"cal"$,
// car la possibilité des alias rend incalculable la redondance d'informations induite par $cal(E)^sharp.double$.
// On a alors aussi, pour $x : $ `*const` $tau$, ou $x : $ `*mut` $tau$ :
// $ #eq_def($#ssems[`storage_live`$(x)$] chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow top], c) | (rho, c) in rho^sharp} chevron.r$) $
// $ #eq_def($#ssems[`storage_dead`$(x)$] chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow bot], c) | (rho, c) in rho^sharp} chevron.r$) $
// $ #eq_def($#ssems($x = e$) chevron.l C, d^sharp, rho^sharp chevron.r$, $chevron.l C, d^sharp, {(rho[x arrow rho(u)], c) | u in #esems($e$) chevron.l C, d^sharp, rho^sharp chevron.r, (rho, c) in rho^sharp} chevron.r$) $
// De cette manière, les alias sont autorisés par assignation directe, i.e. :
// $ rho(u) = rho(x) $
// dans tous les environnements après $#ssems($x = e$)$.
// Puis dans le cas où $x : $ `*mut` $tau$ :
// $ #eq_def($#ssems($*x = e$) chevron.l C, d^sharp, rho^sharp chevron.r$, $union.big_((rho, c) in rho^sharp) union.big_(v in rho(x)) #ssems($v = e$) chevron.l C, d^sharp, {rho} chevron.r$) $
// Cette fois on ne procède pas à un filtrage qui serait trop coûteux car $rho(x)$ peut être arbitrairement plus dense dans le cas de $x : $`*mut` $tau$.
// Et enfin :
// $ #eq_def($#ssems[$x = t$ `as *mut` $tau$] chevron.l C, d^sharp, rho^sharp chevron.r$, $$) $
// $ #eq_def($#ssems[$x = t$ `as *const` $tau$] chevron.l C, d^sharp, rho^sharp chevron.r$, $$) $

#pagebreak()
#bibliography.with(title: "Bibliographie")("rust.bib")