#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "@preview/curryst:0.3.0": rule, proof-tree

#import "functions.typ": *

#set page(
    margin: 1.25in,
    numbering: "1",
)
#set par(
    //leading: 0.55em,
    //spacing: 0.55em,
    //first-line-indent: 1.8em,
    justify: true
)
#set text(
    font: "Tex Gyre Pagella",
    size:11pt
)

#set heading(numbering: "1.")

#show raw: set text(font: "New Computer Modern Mono")

#show heading: set block(above: 1.4em, below: 1em)
#show heading.where(depth:1): body => { pagebreak(weak: true); body}

// Make ":" work like Latex's \colon by default. 
#show sym.colon: it => math.class("punctuation", it)
#let colon = math.class("relation", $:$)

#let theorem    = thmplain("teorema", "Teorema", titlefmt: strong)
#let lemma      = thmplain("lema", "Lema", titlefmt: strong)
//#let definition = thmbox("definição", "Definição", inset: (x: 1.2em, top: 1em))
#let definition = thmplain("definição", "Definição", titlefmt: strong)
#let corollary  = thmplain("corolário", "Corolário", base: "theorem", titlefmt: strong)
#let example    = thmplain("examplo", "Examplo").with(numbering: none)
#let proof      = thmproof("prova", "Prova")

//=================================================


= Autômatos Finitos

#image("imgs/tennis.dot.svg")
#image("imgs/tennis2.dot.svg")

Um autômato finito pode ser descrito
por uma tupla $cal(A) = (Σ, Q, S, F, Δ)$:

/ $Σ$: o alfabeto.
/ $Q$: o conjunto de estados.
/ $S$: o conjunto de estados iniciais.
/ $F$: o conjunto de estados finais.
/ $Δ$: a relação de transição (arestas)

O alfabeto $Σ$ é um conjunto finito de caracteres,
que descreve quais caracteres aparecem nas arestas do autômato.

O conjunto de estados $Q$ deve ser finito,
o que é inclusive a principal limitação dos autômatos finitos.
Os caminhos que percorremos no autômato começam
em um estado de $S$ e terminam em algum estado de $F$.

Uma aresta é uma tripla $(Q × Σ × Q)$,
com o estado de origem, o rótulo, e o estado de destino.
O conjunto $Δ$ descreve uma relação de transição entre estados.
Pense em uma tabela de um banco de dados relacional, em que as colunas são
o estado de origem, o rótulo da aresta, e o estado de destino.

Um *Autômato Finito Determinístico (AFD)*
é um autômato que pode ser simulado sem ter que fazer escolhas.
Ele tem um único estado inicial,
e arestas que saem do mesmo estado sempre tem rótulos diferentes.
Podemos enxegar a relação de transição como uma _função de transição_.
Especificamente, uma função parcial que mapeia $(X,a)$ para o estado de destino $Y$.

Um *Autômato Finito Não-Determinístico (AFND)*
não tem estas restrições.
Eles podem ter mais de um estado inicial
e o conjunto de arestas pode ser uma relação qualquer.
Para testar se uma palavra é reconhecida pelo autômato,
temos que trabalhar com conjuntos de estados,
em vez de um estado só.

obs.: Algumas apresentações de AFD exigem que
a função de transição seja total.
Dá pra fazer isso se introduzirmos um estado morto
que serve de destino para todas as arestas faltantes.

= Caminhos

Um autômato reconhece uma palavra $w$ se existe um caminho
rotulado por $w$, que leva de um estado inicial para um final.
Para formalizar estes conceitos,
podemos definir uma estrutura de dados para os caminhos,
assim como uma função que calcula o rótulo do caminho.

#let pathnil(x)      = $#x!$
#let pathcons(x,a,p) = $#x attach(→, t:#a) #p$

#let ini = $"head"$
#let fin = $"last"$
#let lab = $"str"$
#let ars = $"ars"$

#grid(
    columns:(50%, 50%),
    align:center,

    proof-tree(
        rule(
            $pathnil(X) : X ~> X$,
            //=====
            $X ∈ Q$,
        )
    ),

    proof-tree(
        rule(
            $pathcons(X, a, p) : X ~> Z$,
            //==========
            $X a Y ∈ Δ$,
            $p : Y ~> Z$,
        )
    ),
)

Existem duas formas de construir um caminho sobre um dado autômato:

+ (vazio) Se $X$ é um estado, então $X!$ é um caminho que vai de $X$ até $X$.
+ (passo) Se $X a Y$ é uma aresta de $X$ para $Y$,
   e $p$ é um caminho que vai de $Y$ até $Z$,
   então $pathcons(X, a, p)$ é um caminho que vai de $X$ até $Z$.

Alguns exemplos de caminho:

- $pathcons(E, a, pathcons(A, a, pathnil(X)))$
- $pathcons(E, b, pathcons(B, b, pathnil(X)))$
- $pathcons(E, a, pathcons(A, b, pathcons(E, a, pathcons(A, a, pathnil(X)))))$

Podemos escrever uma função que recupera a palavra percorrida pelo caminho:

$
&lab(pathnil(X)) &&= ε \
&lab(pathcons(X,a,p)) &&= a · lab(p) \
$

Agora estamos prontos para especificar
a linguagem reconhecida por um autômato $cal(A)=(Σ,Q,S,F,δ)$.
Dizemos que ele reconhece a palavra $w$ se existe um caminho $p$
que leva de um estado inicial para um final, lendo a palavra $w$.
Isto é:

- $p : X ~> Z$
- $X ∈ S$
- $Z ∈ F$
- $lab(p) = w$

= Relação de Transição

#let astep = $⊢$
#let asteps = $attach(⊢, tr:*)$

Caminhos representam diretamente a sequência de estados visitados.
No entanto, a função $lab()$ é inconveniente na hora de escrever provas.

Uma outra maneira de especificar o comportamento do autômato é
modelar uma máquina que testa se a palavra é reconhecida pelo autômato.
Esta máquina mantém duas variáveis: o estado atual, e a string do que falta ler.
A relação de transição $⊢$ descreve os passos que a máquina executar.
Quando estamos no estado $X$ e a próxima letra da entrada é $a$,
então se existir uma aresta $X a Y$
nós podemos mudar para o estado $Y$ e consumir a letra $a$.

#grid(
    columns:(100%),
    align:center,

    proof-tree(
        rule(
            $(X, a w) ⊢ (Y, w)$,
            //--------------
            $X a Y ∈ Δ$,
        )
    ),
)

Uma derivação completa consiste de uma sequência destes passos.
Usamos a relação $(X, x) asteps (Z, z)$ para dizer que existe uma
sequência de zero ou mais transições que levam de $(X, x)$ até $(Z, z)$.
No jargão técnico, $asteps$ é o fecho reflexivo e transitivo de $astep$.

#grid(
    columns:(50%, 50%),
    align:center,

    proof-tree(
        rule(
            $(X, w) asteps (X, w)$,
            //----------------
            $$
        )
    ),

    proof-tree(
        rule(
            $(X, x) asteps (Z, z)$,
            //----------------
            $(X, x) astep (Y, y)$,
            $(Y, y) asteps (Z, z)$,
        )
    ),
)

Exemplo de uma derivação completa:

$
  (X, "ababa") ⊢ (Y, "baba") ⊢ (X, "aba") ⊢ (Y, "ba") ⊢ (X, "a") ⊢ (Y, ε)
$

A linguagem das palavras aceitas a partir de um estado $X$
são as palavras que levam de $X$ até um estado final $Z$:

$
  L(X) = { w | (X, w) asteps (Z, ε) ∧ Z∈F }
$

A linguagem aceita pelo autômato é o conjunto das palavras
aceitas por algum dos estados iniciais

$
  L(cal(A)) = union.big_(X ∈ S) L(X)
$

Derivações são tão poderosas quanto caminhos.
É possível escrever um algoritmo que converte de uma para a outra.

$
    "p2d"(#{
        proof-tree(
            rule(
                $pathnil(X) : X ~> X$,
                //=====
                $X ∈ Q$,
            )
        )
    }, w) =& (X, w) asteps (X, w) \

    "p2d"(#{
        proof-tree(
            rule(
                $pathcons(X, a, p) : X ~> Z$,
                //==========
                $X a Y ∈ Δ$,
                $p : Y ~> Z$,
            )
        )
    }, w) =& "let" (Y, y) asteps (Z, z) := "p2d"(p, w) "in" \
           & (X, a y) astep (Y, y) asteps (Z, z)
$

#strong[Exercício:]
Prove que podemos adicionar e remover caracteres do final. Para todo $w$,
$
(X,x) astep (X,y) iff (X,x w) astep (X,y w) \
$

#strong[Exercício:]
Extenda a prova para $asteps$. Para todo $w$,
$
(X,x) asteps (X,y) iff (X,x w) asteps (X,y w) \
$

= Derivações de gramática

#let dmult = $attach(=>, tr:*)$

Esta semântica é comumente usada para linguagens livres de contexto,
mas é raramente usada para linguagens regulares. 

#grid(
    columns:(33%,33%,33%),
    align:center,

    proof-tree(
        rule(
            $X => ε$,
            //--------------
            $X ∈ F$
        )
    ),

    proof-tree(
        rule(
            $X => a Y$,
            //--------------
            $X a Y ∈ Δ$,
        )
    ),

    proof-tree(
        rule(
            $u w v => u w' v$,
            //--------------
            $w => w'$,
        )
    ),
)

Exemplo:

$
  " E" => "aA" => "abE" => "abbB" => "abbbX" => "abbb"
$

É claro, também precisamos definir o fecho reflexivo e transitivo de $=>$.

#grid(
    columns:(33%,33%,33%),
    align:center,

    proof-tree(
        rule(
            $X dmult X$,
            $$
        )
    ),

    proof-tree(
        rule(
            $X dmult Z$,
            //--------------
            $X => Y$,
            $Y dmult Z$,
        )
    ),
)

= Semântica operacional big-step

#let bigstep(X, w) = $#X ⇓ #w$
#let step(X, a, Y) = $#X attach(→, t:#a) #Y$

Em breve vamos escrever várias provas que discorrem sobre
$L(X)$ e é repetitivo ter que escrever toda hora
aquele $(Z, ε) ∧ Z ∈ F$.
Por isso inventei uma notação nova que abrevia isso.
A relação $bigstep(X, w)$ codifica que existe um caminho
que leva de $X$ para algum estado final, lendo $w$.

#grid(
    columns:(50%, 50%),
    align:center,

    proof-tree(
        rule(
            $bigstep(X, ε)$,
            //--------------
            $X ∈ F$
        )
    ),

    proof-tree(
        rule(
            $bigstep(X, a v)$,
            //--------------
            $X a Y ∈ Δ$,
            $bigstep(Y, v)$,
        )
    ),
)

Por extenso:

1. Se $X$ é um estado final, então ele reconhece a palavra vazia.
2. Se existe uma aresta $X a Y$
   e $Y$ reconhece $v$, então $X$ reconhece $a v$.
3. Estados só reconhecem palavras que se encaixam nas regras acima.


#strong[Exercício:] prove que a definição direta de $⇓$
equivale à sua especificação via $asteps$:

$
    bigstep(X, w) iff exists Z: (X, w) asteps (Z, ε) ∧ Z ∈ F  
$


// == Big-step vs small-step
//
//
// Semânticas como a do $⇓$ são o que chamamos de _big step_.
// Em um pulo só, ela relaciona o estado com a string que ele aceita.
// Por outro lado, as semânticas com $astep$ e $=>$ são _small step_,
// pois descrevem um passinho de cada vez.
// Uma diferença entre as duas é que nas semânticas small step
// precisamos ser capazes de representar as configurações intermediárias da computação.
// Na semântica $astep$ esta configuração é uma tupla de estado e string restante,
// enquanto na semântica $=>$ a configuração contém
// a string já lida seguida pelo estado atual.
// 
// As abordagens big-step e small-step tem seus prós e contras.
// Semânticas big-step podem resultar em provas mais simples,
// já que usamos uma relação só,
// enquanto na big-step tem duas relações, uma com e outra sem a estrela.
// A principal vantagem as semânticas small step é que são
// mais capazes de lidar com loops infinitos.
// Outro atrativo, mais de notação,
// é que dá para escrever a derivação completa horizontalmente em uma linha só.


= Semântica via sistemas de equações.

Semânticas operacionais
exigem que nós rodemos um programa de computador para saber se uma palavra é aceita.
Os detalhes dependem da implementação deste programa de computador.
Até agora já vimos mais de uma versão:
a semântica com  $astep$, a com $=>$, e a com $⇓$.

Uma outra maneira de pensar sobre a semântica do autômato
é especificar quais propriedades nós gostaríamos que fossem verdade
sobre as linguagens reconhecidas por cada estado.
A especificação da relação $⇓$ parece ser um bom começo:

#[
#set enum(numbering: "a)")
1. Se $X$ é um estado final, então ele deve reconhecer a palavra vazia.
2. Se existe uma aresta $X a Y$
   e $Y$ reconhece $v$, então $X$ deve reconhecer $a v$.
3. Estados só reconhecem palavras que se encaixam nas regras acima.
]

Buscamos atribuir uma linguagem à cada estado, obedecendo estas regras.
As restrições (a) e (b) dizem quando a solução proposta é factível.
Já a regra (c) diz que buscamos a solução mais simples dentre as factíveis.


#image("imgs/aba.dot.svg")

Vamos tentar escrever essas restrições diretamente,
usando o autômato acima como exemplo.
Buscamos uma função $L: Q -> Σ^*$ que atribui uma linguagem para cada estado.
As regras (a) e (b) nos dizem que valores de $L(X)$ e $L(Y)$ são aceitáveis.

+ $ε ∈ L(Y)$
+ $v ∈ L(Y) implies "a" · v ∈ L(X)$
+ $v ∈ L(X) implies "b" · v ∈ L(Y)$

Devemos tomar cuidado para não confundir
os estados de entrada e saída de cada aresta.
Vamos ler com calma o que cada uma dessas fórmulas diz.

+ A linguagem de Y deve conter a palavra vazia.
+ Para mostrar que uma palavra começando em "a" pertence à linguagem de X,
    é~suficiente mostrar que o resto desta palavra pertence à linguagem de Y.
+ Para mostrar que uma palavra começando em "b" pertence à linguagem de Y,
    é~suficiente mostrar que o resto desta palavra pertence à linguagem de X.

Uma solução trivial é dizer que qualquer estado aceita qualquer palavra. 

+ $L(X) = Σ^*$
+ $L(Y) = Σ^*$

Uma solução mais esperta é

+ $L(X) = "a"("b" "a"^*)$
+ $L(Y) = ("b" "a"^*)$

Vamos conferir:

+ $ε ∈ ("b" "a"^*)$
+ $v ∈ ("b" "a"^*) implies "a" · v ∈ "a"("b" "a"^*)$
+ $v ∈ "a"("b" "a"^*) implies "b" · v ∈ ("b" "a"^*)$

Esta solução que encontramos não é somente uma solução esperta,
ela é a mais esperta de todas! Podemos mostrar que qualquer
solução aceitável contém esta solução como sub-solução.
Isto é, se $L$ é aceitável então

$
  "a"("b" "a"^*) ⊆ L(X) \
     ("b" "a"^*) ⊆ L(Y)
$

Nossa prova será por indução no comprimento das palavras de $L$.
Para tal, é melhor escrever o enunciado em termos de "$w∈$".
Ou seja, se assumirmos como hipótese que $L$ é factível

+ $ε ∈ L(Y)$
+ $v ∈ L(Y) implies "a" · v ∈ L(X)$
+ $v ∈ L(X) implies "b" · v ∈ L(Y)$

então para todo $w$ vale

$
  (A) w ∈ "a"("b" "a"^*) implies w ∈ L(X) \
  (B) w ∈    ("b" "a"^*) implies w ∈ L(Y)
$

A indução tem que tratar três casos:

- $w=ε$.
  A implicação (A) vale vacuosamente pois $ε ∉ "a"("b" "a"^*)$.
  A implicação (B) vale pois a hipótese (1) garante que $ε ∈ L(Y)$.

- $w="a" v$.
  Primeiro mostramos que $"a" v ∈ "a"("b" "a"^*) implies "a" v ∈ L(X)$.
  Quando $"a"v ∈ "a"("b" "a"^*)$, necessariamente $v ∈ ("b" "a"^*)$.
  Como $v$ é uma palavra mais curta, podemos aplicar a hipótese de indução
  para obter $v ∈ L(Y)$. Pela regra (2) da especificação de factível,
  concluímos $"a" v ∈ L(X)$.

  A segunda implicação, $w ∈ ("b" "a"^*) implies w ∈ L(Y)$,
  vale vacuosamente pois palavras que começam com "a" nunca casam com $("b" "a"^*)$.

- $w="b" v$.
  A prova é análoga à do caso anterior.
  A implicação (A) vale vacuosamente,
  e a implicação (B) segue da hipótese de indução junto com a regra (3).


== Sistemas

Agora vou reescrever as restrições para deixar num formato mais limpo.
Primeiramente, vou omitir os $L()$ das fórmulas.
Nem o Germán Cano aguenta escrever tanto L.
Daqui pra frente, pode assumir que se eu escrever um estado
num contexto que espera um conjunto/linguagem, na verdade é um $L(X)$ 

+ $ε ∈ Y$
+ $"a" · v ∈ X impliedby v ∈ Y$
+ $"b" · v ∈ Y impliedby v ∈ X$

Podemos trocar as implicações por subconjuntos:

+ $Y ⊇ {ε}$
+ $X ⊇ "a" · Y$
+ $Y ⊇ "b" · X$

Dá pra juntar as restrições
para que haja só uma por variável.

+ $X ⊇ "a" · Y$
+ $Y ⊇ "b" · X ∪ {ε}$




então podemos con

= Semântica Denotacional

Vou fazer as provas para este autômato específico.
#image("imgs/bb.dot.svg")

#let den(x) = $⟦#x⟧$

Queremos encontrar a menor solução para o sistema
$den(X) = {ε} ∪ a · den(X)$.

Mais formalmente, o menor ponto fixo do operador $f(X) = {ε} ∪ a · X$

== Prova de que é ponto fixo

Para provar que a semântica operacional casa com a denotacional,
o primeiro passo é mostrar que a linguagem descrita pela semântica operacional
é uma solução do sistema de equações pedido pela semântica denotacional.

#block(breakable:false)[

    #theorem[
        $f({w | bigstep(X, w)}) = {w | bigstep(X, w)}$
    ]
    #proof[
        Um caminho do estado $X$ até um estado final tem duas formas possíveis.
        Ou $X$ é o estado final do caminho ($bigstep(X, ε)$),
        ou visitamos uma aresta e em seguida vamos para o estado final:
        $bigstep(X, a v)$, com $step(X, a, X)$ e $bigstep(X, v)$.
    ]
    $
        &{w | bigstep(X, w)} \
        &= #[(dois casos possíveis)] \
        & {ε} ∪ {a v | bigstep(X, v)} \
        &= #[(definição de concatenação)] \
        & {ε} ∪ a · {v | bigstep(X, v)} \
        &= #[(renomear)] \
        & {ε} ∪ a · {w | bigstep(X, w)} \
    $
]


== Prova de que é o menor ponto fixo

#block(breakable:false)[
    #let lfp=$μ F$

    Só falta mostrar que a semântica operacional descreve
    a menor solução possível.

    #theorem[
        Se R é um ponto fixo de $F$,
        então ${w | bigstep(X, w)} ⊆ R$
    ]
    #proof[
        A intuição por trás da prova é que podemos expendir $R$
        usando a propriedade de ser ponto fixo
        e observar que as palavras de ${w | bigstep(X, w)}$
        surgem uma a uma, e portanto pertencem ao conjunto $R$.

        $
            R &= ε ∪ a R \
              &= ε ∪ a (ε ∪ a R) \
              &= ε ∪ a ∪ a^2 (ε ∪ a R) \
              &= ε ∪ a ∪ a^2 ∪ a^3 (ε ∪ a R) \
              &= ...
        $

        A prova completa é por indução estrutural sobre a derivação $bigstep(X, w)$.
        No caso base temos $bigstep(X, ε)$ e queremos provar $ε ∈ R$.

        $
            & ε ∈ R \
            & <=> #[($R$ é ponto fixo)] \
            & ε ∈ ({ε} ∪ a · R) \
            & ⇐ \
            & e ∈ {ε} \

        $

        No caso indutivo temos $bigstep(X, a v)$,
        oriundo de $step(X, a, X)$ e $bigstep(X, v)$,
        e queremos provar provar que $a v ∈ R$.
        Podemos assumir, pela hipótese de indução, que $v ∈ R$.
        $
            & a v ∈ R \
            & <=> "(R é ponto fixo)" \
            & a v ∈ ({ε} ∪ a · R) \
            & ⇐ \
            & a v ∈ a · R \
            & ⇐ \
            & v ∈ R
        $
    ]
]


= Semântica Denotacional (geral)

Agora voou fazer a prova para o caso geral.

#let lfp=$μ F$

Queremos mostrar que nossa semântica denotacional é compatível com a operacional.
No caso geral, a semântica denotacional descreve um sistema de equações,
com uma linguagem por estado. Buscamos a menor solução do sistema.
$
    ⟦X⟧ = φ(X) ∪ union.big_(X a Y ∈ Δ) a · ⟦Y⟧ \
$

Nosso objetivo é mostar que esta menor solução é 
a linguagem das palavras aceitas pelo autômato operacionalmente:
$⟦X⟧ = L(X)$.

== Prova de que é o menor ponto fixo (big step)

#lemma[
    As linguagens da semântica operacional formam uma solução
    do sistema de equações da semântica denotacional.
    Isto é, para todo estado X,

    $ L(X) = φ(X) ∪ union.big_(X a Y ∈ Δ) a · L(Y) . $
]
#proof[
    O principal truque é que $bigstep(X, w)$
    tem dois casos possíveis: $bigstep(X, ε)$ e $bigstep(X, a v)$.

    No primeiro, a unificação nos diz que $X$ deve ser estado final e $w=ε$.
    No segundo, temos que $w$ precisa começar com alguma letra $a$
    e deve existir uma aresta $X a Y$ e a linguagem de $Y$ deve aceitar o resto da palavra..

    $
        & L(X) \
        = & #[(por definição)]\
        & {w | bigstep(X, w)}\
        = & #[(quebrar em casos)]\
        & {ε | X ∈ F} ∪  { a v | X a Y ∈ Δ ∧ bigstep(Y, v) } \
        = & #[(mover o $ forall X a Y$ para fora da expressão)]\
        & {ε | X ∈ F} ∪
        union.big_(X a Y ∈ Δ) a · { v | bigstep(Y, v) } \
        = & #[(definições de $φ(X)$ e de $L(Y)$)]\
        & φ(X) ∪
        union.big_(X a Y ∈ Δ) a · L(Y) \



    $
]

#lemma[
    As linguagens da semântica operacional são um lower bound
    do sistema de equações da semântica denotacional.

    $
        cal(F)(R) ≤ R ==> L ≤ R
    $
]

#proof[
    Primeiro, devemos massagear o enunciado. Nossa hípótese é:

    $
      H: (φ(X) ∪ union.big_(X a Y ∈ Δ) a · R(Y)) ⊆ R(X)
    $

    em outras palavras:

    $
    H_1:& forall X: φ(X) ⊆ R(X) \
    H_2:& forall X a Y: (X a Y ∈ Δ) ==> a R(Y) ⊆ R(X)
    $

    Assumindo $H_1$ e $H_2$, queremos mostrar que,
    para todo $X$ e $w$,

    $
        bigstep(X, w) ==> w ∈ R(Y)
    $

    A prova é por indução em $bigstep(X,w)$.

    No caso base, temos $w=ε$ e $X∈F$.
    Portanto, por $H_1$, $w ∈ φ(X) ⊆ R(X)$

    No caso indutivo, temos $w = a v$ e
    existe uma aresta $X a Y$ tal que $bigstep(Y, v)$.
    Pela hipótese de indução, $v ∈ R(Y)$.
    Portanto, por $H_2$, $w = a v ∈ a R(Y) ⊆ R(X)$.
]

#proof[
    Primeiro, devemos massagear o enunciado

    Se para todo $X$, $(φ(X) ∪ union.big_(X a Y ∈ Δ) a · R(Y)) ⊆ R(X)$, \
    então para todo $X$, $L(X) ⊆ L(X)$.

    Se para todos $X, w$,
    $
    (w∈φ(X) ∨ exists X a Y∈Δ : w ∈ a · R(Y)) ==> w ∈ R(X)
    $

    então para todos $X,Z,w$,
    $ ( (X,w) asteps (Z, ε) ∧ Z∈F) ==> w ∈ R(X) $

    A prova é por indução na evidência $(X,w) asteps (Z, ε)$

    No caso base, temos $X=Z$ e $w=ε$.
    Como $Z$ é final, $X$ também é.
    Portanto, $w∈φ(X)$ e a hipótese nos permite concluir $w ∈ R(X)$.

    No caso indutivo, temos
    $(X,w) asteps (Z, ε)$ = $(X,a v) astep (Y, v) asteps (Z, ε)$.
    Portanto, existe uma aresta $X a Y$ que leva de $X$ a $Y$,
    e sabemos que $w$ começa com $a$ ($w = a v$).
    Aplicando a hipótese de indução em $(Y, v) asteps (Z, ε)$,
    deduzimos que $v ∈ R(Y)$. Logo, $w = a v ∈ a · R(Y)$.
    Com isso, podemos aplicar a hipótese $H$ e obter $w ∈ R(X)$.
]


== Prova de que é o menor ponto fixo (derivações)


#let lfp=$μ F$

Queremos mostrar que nossa semântica denotacional é compatível com a operacional.
Isto é, o menor ponto fixo do sistema de equações
é a linguagem das palavras reconhecidas pelo autômato.

O sistema:
$
    ⟦X⟧ = φ(X) ∪ union.big_(X a Y ∈ Δ) a · ⟦Y⟧ \
$

#lemma[
    As linguagens da semântica operacional formam uma solução
    do sistema de equações da semântica denotacional.
    Isto é, para todo estado X,

    $ L(X) = φ(X) ∪ union.big_(X a Y ∈ Δ) a · L(Y) . $
]
#proof[
    O principal truque é quebrar a derivação $(X,w) asteps (Z,ε)$ em dois casos:
    + $(X, w) asteps (Y, ε)$ = $(Z, ε) astep (Z, ε)$
    + $(X, w) asteps (Y, ε)$ = $(Z, a v) astep (Y, v) asteps (Z, ε)$
    No primeiro, a unificação nos diz que $X=Z$ e $w=ε$.
    No segundo, temos que $w$ precisa começar com alguma letra $a$
    e deve existir uma aresta $X a Y$.

    $
        & L(X) \
        = & #[(definição da semântica operacional)]\
        & {w | (X, w) asteps (Z, ε) ∧ Z ∈ F}\
        = & #[(quebrar em casos)]\

        & {ε | (X, ε) asteps (X, ε) ∧ x ∈ F} ∪ \
        & { a v | (X, a v) astep (Y, v) asteps (Z, ε)
                ∧ X a Y ∈ Δ ∧ Z ∈ F } \
        = & #[(simplificar)]\
        & {ε | X ∈ F} ∪
        { a v | (Y, v) asteps (Z, ε)
                ∧ X a Y ∈ Δ ∧ Z ∈ F } \
        = & #[(mover o $ forall X a Y$ para fora da expressão)]\
        & {ε | X ∈ F} ∪
        union.big_(X a Y ∈ Δ) a · { v | (Y, v) asteps (Z, ε) ∧ Z ∈ F } \
        = & #[(definições de $φ(X)$ e de $L(Y)$)]\
        & φ(X) ∪
        union.big_(X a Y ∈ Δ) a · L(Y) \



    $
]

#lemma[
    As linguagens da semântica operacional são um lower bound
    do sistema de equações da semântica denotacional.

    $
        cal(F)(R) ≤ R ==> L ≤ R
    $
]
#proof[
    Primeiro, devemos massagear o enunciado

    Se para todo $X$, $(φ(X) ∪ union.big_(X a Y ∈ Δ) a · R(Y)) ⊆ R(X)$, \
    então para todo $X$, $L(X) ⊆ L(X)$.

    Se para todos $X, w$,
    $
    (w∈φ(X) ∨ exists X a Y∈Δ : w ∈ a · R(Y)) ==> w ∈ R(X)
    $

    então para todos $X,Z,w$,
    $ ( (X,w) asteps (Z, ε) ∧ Z∈F) ==> w ∈ R(X) $

    A prova é por indução na evidência $(X,w) asteps (Z, ε)$

    No caso base, temos $X=Z$ e $w=ε$.
    Como $Z$ é final, $X$ também é.
    Portanto, $w∈φ(X)$ e a hipótese nos permite concluir $w ∈ R(X)$.

    No caso indutivo, temos
    $(X,w) asteps (Z, ε)$ = $(X,a v) astep (Y, v) asteps (Z, ε)$.
    Portanto, existe uma aresta $X a Y$ que leva de $X$ a $Y$,
    e sabemos que $w$ começa com $a$ ($w = a v$).
    Aplicando a hipótese de indução em $(Y, v) asteps (Z, ε)$,
    deduzimos que $v ∈ R(Y)$. Logo, $w = a v ∈ a · R(Y)$.
    Com isso, podemos aplicar a hipótese $H$ e obter $w ∈ R(X)$.
]


= Lema de Arden

#lemma[
    $X=A^*B$ é solução da equação $X = A X ∪ B$.
] <thm:arden-solution>
#proof[
    $
    X & = A^* B\
    & = (union.big_(i=0)^(∞) A^i B) \
    & = (union.big_(i=1)^(∞) A^i B) ∪ A^0 B \
    & = A · (union.big_(i=0)^(∞) A^i B) ∪ B \
    & = A · (A^*B) ∪ B \
    & = A X ∪ B \

    $
]


Falta mostrar que $A^*B$ é a menor solução.
Isto é, qualquer solução de $X = A X ∪ B$ contém $A^*B$.
A intuição para isso aparece quando substituímos $X$ por #box[$A X ∪ B$] sucessivamente.
Repare que na expansão de $X$ os termos de $A^*B$
vão aparecendo um por um: $A^0 B, A^1 B, A^2 B, ...$.

$
                                             X &= \
                            A^1 X ∪ underline(B) &= A^1 (A X ∪ B) ∪ B = \
                    A^2 X ∪ underline(A B ∪ B) &= A^2 (A X ∪ B) ∪ A B ∪ B =\
            A^3 X ∪ underline(A^2 B ∪ A B ∪ B) &= A^3 (A X ∪ B) ∪ A^2 B ∪ A B ∪ B = \
    A^4 X ∪ underline(A^3 B ∪ A^2 B ∪ A B ∪ B) &= ... \
$

Para a prova formal, expandimos a definição de $A^*B$ cxomo uma
união infinita e mostramos que todos seus componentes $A^n B$
estão contidos em $X$.

#lemma[
    Se $A X ∪ B ⊆ X $ então $A^*B ⊆ X$.
] <thm:arden-least>
#proof[
    Nosso objetivo é mostrar que
    $union.big_(i=0)^(∞) A^i B ⊆ X$ .
    Para tal, podemos mostrar
    que $A^n B ⊆ X$ vale para todo $n$,
    por indução em $n$.
    Afinal, se o conjunto $X$ contém todos os $A^n B$,
    ele deve ser maior ou igual a $union.big_(i=0)^(∞) A^i B$,
    que por definição é o menor conjunto com esta propriedade.

    #emph[Caso base:] $n=0$

    $A^0 B = B ⊆ A X ∪ B ⊆ X$

    #emph[Caso indutivo:] $n ≥ 1$

    Pela hipótese de indução, podemos assumir $A^(n-1) B ⊆ X$.
    Concatenando $A$ dos dois lados, obtemos $A^n B ⊆ A X$.
    Portanto, $A^n B ⊆ A X ⊆ A X ∪ B ⊆ X$.
]

Finalmente, provamos o lema de Arden propriamente dito.

#theorem("Lema de Arden")[
    $A^*B$ é a menor solução de $X = A X ∪ B$.
] <thm:arden>
#proof[
    O @thm:arden-solution nos diz que $A^*B$ é solução
    e o @thm:arden-least nos diz que $A^*B$ é a menor solução.
]

== Por que a menor solução?

Tivemos um bom trabalho para especificar
que buscamos a menor solução, e não meramente uma solução qualquer.
O que justifica este esforço? Em que casos existem outras soluções
para $X = A X ∪ B$, além da menor solução $A^*B$?
Um exemplo é a equação

$
X = X ∪ {a}
$

A menor solução é o conjunto ${a}$.
No entanto, também são soluções todos os superconjuntos de ${a}$:
por exemplo, ${a, b}$ e $Σ&^*$ também são soluções.
A culpa disso está no $X=X$ da equação,
que corresponde a um loop vazio no autômato.

Como vimos anteriormente, a menor solução
surge dos termos $A^i B$ da expansão de $X$.
Para obtermos uma solução diferente de $A^* B$,
é preciso que existam palavras oriundas da parte $A^n X$ da expansão.
Isto só é possível quando o conjunto $A$ contém a palavra vazia $ε$.
Nossa prova começa com um lema auxiliar que desenrrola a equação $n$ vezes.

#lemma[
    Se $X ⊆ A X ∪ B$, então
    $forall n ≥ 0. (X ⊆ A^(n+1) X ∪ (union.big_(i=0)^(n) A^i B))$
] <thm:arden-length>
#proof[
    Como sempre, indução em $n$.

    #emph[Caso base:] $n=0$

    $
    X &⊆ A X ∪ B \
      &= A^(0+1) X ∪ (union.big_(i=0)^(0) A^i B)
    $

    #emph[Caso indutivo:] $n≥1$

    $
    X & ⊆ A^((n-1)+1) X ∪ (union.big_(i=0)^(n-1) A^i B) = A^n X ∪ (union.big_(i=0)^(n-1) A^i B) \
      & ⊆ A^n (A X ∪ B)  ∪ (union.big_(i=0)^(n-1) A^i B) \
      & = A^(n+1) X ∪ A^n B ∪ (union.big_(i=0)^(n-1) A^i B) \
      & = A^(n+1) X ∪ (union.big_(i=0)^n A^i B) \
    $
]

Agora podemos mostrar que se $A$ não contém a palavra vazia,
então todas as soluções do sistema estão dentro de $A^*B$.

#lemma[
    Se $ε ∉ A$, e $X ⊆ A X ∪ B$,
    então $X ⊆ A^*B$.
] <thm:arden-greatest>

#proof[
   Seja $w$ uma palavra de $X$,
   e seja $abs(w)$ o seu comprimento.
   Pelo @thm:arden-greatest, deduzimos que $w ∈  A^(abs(w)+1) X ∪ (union.big_(i=0)^(abs(w)) A^i B)$.
   Mas lembre que, como $ε ∉ A$,
   então $A$ só contém palavras com comprimento maior ou igual a 1.
   Portanto, $A^(abs(w)+1) X$ só contém palavras com comprimento
   pelo menos $abs(w)+1$, o que impede que $w$ pertença a $A^(abs(w)+1) X$.
   Concluimos que $w ∈ union.big_(i=0)^(abs(w)) A^i B$,
   que por sua vez está contido em $A^* B$.
]

Finalmente, podemos enunciar a versão tradicional do lema de Arden.

#theorem[
    Se $ε ∉ A$, e $X = A X ∪ B$,
    então $X = A^*B$.
] <thm:full-arden>
#proof[
    Segue do @thm:arden-solution, @thm:arden-least, e @thm:arden-greatest.
]

Curiosidade: O @thm:arden-greatest depende crucialmente das palavras terem comprimento finito.
Se permitíssemos strings contendo sequências infinitas de caracteres,
equações como $X = a X$ permitiriam soluções infinitas como "$a a a ...$".
Nestas notas de aula, nós não permitimos e nem permitiremos estas strings infinitas.
No entanto, eu queria deixar registrado que existem sim situações
em que falar de strings infinitas faz sentido.
Essa escolha levaria a um teoria alternativa,
que trabalharia com maiores pontos fixos ao invés de menores pontos fixos,
e provas por co-indução ao invés de por indução.


/////////////////////
= Transições vazias
/////////////////////

O autômato a seguir reconhece a linguagem $a^* b^*$.
Porém, isso pode não ser tão óbvio...

#image("imgs/epsilon2.dot.svg")

Seria legal se pudesemmos construir um autômato que tem
uma parte responsável pelo $a^*$ e uma pelo $b^*$.
Uma ferramenta que possibilita isso são arestas $ε$:

#image("imgs/epsilon1.dot.svg")

Repare que agora, o autômato é a sequência de dois sub-autômatos.
Temos um único estado final, e cada letra da expressão regular $a^* b^*$
corresponde a uma única aresta.

== Eliminando transições ε

Transições ε podem permitir uma representação do autômato com menos arestas,
porém não introduzem nenhum poder adicional.
Todo autômato com transição $ε$ pode ser reescrito em um autômato equivalente sem $ε$.

$
  A &= a A ∪ B \
  B &= b B ∪ ε \
$

Agora, substituímos a definição de B na equação de A:

$
  A &= a A ∪ (b B ∪ ε) \
  B &= b B ∪ ε \
$

Voilá! Chegamos na versão do autômato sem transição ε.
Resumidamente, o estado A herdou todas as transições do estado B,
que pode ser alcançado "de graça" a partir de A.

== Loops ε



Tome  cuidado com autômatos que tem ciclos de arestas $ε$,
pois nesses casos a regra da substituição não é suficiente.


#image("imgs/epsilon-loop1.dot.svg")

$
  X &= X + a B \
$

Quando chegamos nesse ponto, a solução é usar o Lema de Arden.

#image("imgs/epsilon-loop2.dot.svg")

$
  X &= ε X ∪ a B = (ε^*) a B = a B \
$

== Remoção de loops ε maiores

#image("imgs/epsilon-bigloop1.dot.svg")

Uma outra situação interessante ocorre quando temos um loop ε com mais de um estado:

$
  X &= Y + a A \
  Y &= Z + b B \
  Z &= X + c C \
$

Podemos aplicar a substituição várias vezes até fechar o ciclo:

$
  X &= a A + b B + Z \
  Y &= b B + c C + X \
  Z &= a A + c C + Y \
$

$
  X &= a A + b B + c C + X \
  Y &= a A + b B + c C + Y \
  Z &= a A + b B + c C + Z \
$

E em seguida, o lema de Arden remove os auto-ciclos

$
  X &= a A + b B + c C \
  Y &= a A + b B + c C \
  Z &= a A + b B + c C \
$

Como os estados são equivalentes,
podemos combiná-los em um estado só:

$
  X &= a A + b B + c C \
  Y &= X \
  Z &= X \
$

O resultado final é um único estado,
que contém todas as transições dos estados que participavam daquele loop ε

#image("imgs/epsilon-bigloop2.dot.svg")

== Uma prova de $(a^*)^* = (a^*)$

Esta técnica oferece uma prova elegante de que $(a^*)^* = a^*$

$
  X = (a^*)^*
$

$
  X &= (a^*)X + ε
$

$
  X &= Y + ε \
  Y &= (a^*)X \
$

$
  X &= Y + ε \
  Y &= a Y + X \
$

$
  X &= a Y + ε + X \
  Y &= a Y + ε + Y \
$

$
  X &= a Y + ε \
  Y &= a Y + ε \
$

$
  X &= Y \
  Y &= a^* \
$

$
  X &= a^* \
$


/////////////////////
= Pontos Fixos
/////////////////////

Como vimos anteriormente, podemos usar sistemas de equações
para calcular a linguagem de um autômato,
ou o autômato de uma linguagem,
ou mesmo para mostrar que dois autômatos reconhecem a mesma linguagem.

No entanto, um leitor mais desconfiado talvez já tenha se perguntado:
podemos mesmo manipular os sistemas de equação desta forma?
Afinal de contas, não estamos lidando meramente com sistemas comuns,
mas sistemas para o qual buscamos a solução menor / mais simples.
Talvez seja fácil de se convencer que,
após uma operação como substitição de variável,
a solução do antigo sistema também é uma solução do novo sistema.
Mas quem disse que ela também é a #emph[menor] solução do novo sistema?

Neste capítulo veremos que sim,
as maneiras de manipular sistemas que vimos nos capítulos anteriores são válidas.
Mas para tal, precisaremos introduzir uma teoria matemática mais robusta.


== Conjuntos Parcialmente Ordenados

Na matemática,
às vezes é mais fácil trabalhar com uma forma mais geral do problema,
pois ela tem menos "partes móveis" e evidencia quais são as propriedades
que são essenciais para provar os teoremas de nosso interesse.

O primeiro ponto diz sobre o conjunto dos objetos que são candidatos
a solução dos nossos sistemas de equação. No contexto de linguagens
formais, os nossos objetos são linguagens (subconjuntos de $Σ^*$),
e dizemos que uma linguagem é mais simples que a outra
quando a primeira é subconjunto da segunda.
Podemos generalizar esta ideia para evidenciar
que a questão mais central é que existe uma maneira de ordenar linguagens,
e não o fato de que as linguagens são conjuntos de palavras.

#definition[Conjunto Parcialmente Ordenado][
    Um #emph[conjunto parcialmente ordenado],
    (abreviação: #emph[poset]),
    é um par $(A, ≤)$ que consiste de um conjunto $A$
    e uma relação $≤$ que descreve uma ordem parcial entre os elementos de $A$:

    - Reflexividade: $a ≤ a$
    - Transitividade: se $a ≤ b$ e $b ≤ c$ então $a ≤ c$
    - Anti-simetria: se $a ≤ b$ e $b ≤ a$ então $a = b$
]

A ordem parcial não precisa ser uma ordem total, como ocorre nos números naturais.
Lá, também podemos sempre dizer que
para quaisquer $a$ e $b$, vale $a ≤ b$ ou $b ≤ a$.
Já no caso dos conjuntos ordenados por $⊆$, é comum encontrar sistuações em que
nem~$a$ nem~$b$ são subconjuntos um do outro.


== Funções monotônicas

#definition[Função Monotônica][
    Uma função $F:A→B$ é dita #emph[monotônica]
    se para todo $x ≤ y$,
    temos $F(x) prec.eq F(y)$
]

Se interpretarmos a ordem $x≤y$ como "y tem mais informação que x",
as função monotônicas são aquelas em que uma entrada com mais informação
leva a uma saída com mais informação.

Exercício: mostre que as operações de
concatenação, união, e estrela de Kleene
são monotônicas.

Um dos principais motivos do nosso interesse pelas funções monotônicas
é que podemos usá-las para construir sequências crescentes.

$
⊥  ≤ F(⊥) ≤ F^2(⊥) ≤ F^3(⊥) ≤ ...
$

Quando temos uma sequência crescente e limitada, podemos tratar
matemáticamente sobre o limite para qual ela tende no infinito.
Este limite é uma maneira de fundamentar o menor ponto fixo que
obedece $F(x) = x$, sem usar uma definição auto-recursiva,
que potencialmente seria vulnerável a paradoxos matemáticos.


== Pontos fixos

Dada uma endofunção $f:A→A$,
dizemos que um valor $x ∈ A$ é:

#definition[Ponto fixo][quando $f(x) = x$.]
#definition[Ponto pré-fixo][quando $f(x) ≤ x$.]
#definition[Ponto pós-fixo][quando $x ≤ f(x)$.]

#let lfp(f) = $μ #f$
#let gfp(f) = $ν #f$

#definition[Menor ponto pré-fixo][
    Escrevemos $lfp(f)$ para denominar o menor ponto pré-fixo de uma função $f$.
    Ele segue as seguintes regras:
    - (computação): $f(lfp(f)) ≤ lfp(f)$
    - (indução): $f(x) ≤ x → lfp(f) ≤ x$
]

#theorem[
    O menor ponto pré-fixo de uma função monotônica $F$ é único.
]

#proof[
    Suponha que $x$ e $y$ são menores pontos fixos de $F$.
    Pela regra da computação, $y$ é um ponto pré-fixo.
    Logo, pela regra de indução, devemos ter $x ≤ y$.
    Podemos usar um argumento similar para provar $y ≤ x$.
    Concluímos, por antisimetria, que $x=y$.
]

O seguinte teorema nos diz que para mostrar que um valor é o menor ponto fixo,
é suficiente mostrar que ele é o menor ponto pré-fixo, pois ambos coincidem.
Também nos permite usar a notação $lfp(f)$ para se referir
tanto para o menor ponto pré-fixo quanto para o menor ponto fixo.

#theorem[
    O menor ponto pré-fixo de uma função monotônica $F$ também é
    o seu menor ponto fixo.
]

#proof[
    Um ponto fixo é um ponto que é tanto pré-fixo quanto pós-fixo.
    Para mostrar que o menor ponto pré-fixo coincide com o menor ponto fixo,
    basta mostrar que o menor ponto pré-fixo também é um ponto pós-fixo.

    $
    & lfp(f) ≤ f(lfp(f)) \
    & ⇐ f(f(lfp(f))) ≤ f(lfp(f)) \
    & ⇐ f(lfp(f)) ≤ lfp(f) \
    $
]


