
#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "@preview/curryst:0.3.0": rule, proof-tree


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

Um autômato finito é uma tupla $cal(A) = (Σ, Q, S, F, Δ)$, que contém:

/ $Σ$: o alfabeto.
/ $Q$: o conjunto de estados.
/ $S$: o conjunto de estados iniciais.
/ $F$: o conjunto de estados finais.
/ $Δ$: o conjunto de arestas.

O alfabeto $Σ$ é um conjunto finito de caracteres,
que descreve quais caracteres aparecem nas arestas do autômato.

O conjunto de estados $Q$ deve ser finito, 
o que é inclusive a principal limitação dos autômatos finitos.
Os caminhos que percorremos no autômato começam
em um estado de $S$ e terminam em algum estado de $F$.

Uma aresta é uma tripla da forma $(Q × Σ × Q)$.
O conjunto $Δ$ descreve uma relação de transição entre estados.
Pense em uma tabela de um banco de dados relacional,
em que as linhas são as arestas,
e as colunas são o estado de origem, o estado de destino, e o caractere.

Um *Autômato Finito Determinístico (AFD)*
tem um único estado inicial,
e o conjunto de arestas é uma função parcial de $X$ e $a$:
dados $X$ e $a$, existe no máximo um $Y$ tal que $(X,a,Y) ∈ Δ$.

Um *Autômato Finito Não-Determinístico (AFND)*
não tem estas restrições.
Eles podem ter mais de um estado inicial
e o conjunto de arestas pode ser uma relação qualquer.

obs.: Algumas apresentações de AFD exigem que
a função de transição seja total.
Dá pra fazer isso se introduzirmos um estado morto
que serve de destino para todas as arestas faltantes.

= Caminhos

Um autômato reconhece uma palavra $w$ se existe um caminho
rotulado por $w$, que leva de um estado inicial para um final.
Para formalizar estes conceitos,
precisamos definir uma estrutura de dados para os caminhos,
assim como funções que calculam o início e fim de um caminho,
assim como o seu rótulo.

#let arr(a) = $attach(→, t:#a)$
#let pathnil(x) = $#x!$
#let pathcons(x,a,p) = $#x arr(#a) #p$

#let ini = $"ini"$
#let fin = $"fin"$
#let lab = $"lab"$
#let ars = $"ars"$

Alguns exemplos de caminho:

- $pathcons(E, a, pathcons(A, a, pathnil(X)))$
- $pathcons(E, b, pathcons(B, b, pathnil(X)))$
- $pathcons(E, a, pathcons(A, b, pathcons(E, a, pathcons(A, a, pathnil(X)))))$


Para formalizar o que é um caminho,
iremos apresentar uma definição indutiva.
Esta técnica nos permite escrever funções recursivas sobre caminhos,
assim como provas por indução sobre os caminhos. 
Em suma, um *caminho* tem duas possíveis formas:

1. $pathnil(q)$ é um caminho vazio, que começa e termina em $q$.
2. $pathcons(x,a,p)$
    é um caminho que começa em $x$,
    passa por uma aresta rotulada por $a$,
    e continua pelo sub-caminho $p$.

As seguintes funções recursivas calculam, respectivamente:
o estado inicial,
o estado final,
a string percorrida,
e o conjunto de arestas percorridas.

#grid(
    columns: (50%, 50%),
    row-gutter: 2em,

    $
    &ini(pathnil(q)) &&= q \
    &ini(pathcons(q,a,P)) &&= q \
    $,

    $
    &fin(pathnil(q)) &&= q \
    &fin(pathcons(q,a,P)) &&= fin(P) \
    $,

    $
    &lab(pathnil(q)) &&= ε \
    &lab(pathcons(q,a,P)) &&= a · lab(P) \
    $,

    $
    &ars(pathnil(q)) &&= {} \
    &ars(pathcons(q,a,P)) &&= {(q, a, ini(P))} ∪ ars(P) \
    $,
)

Agora estamos prontos para usar esta definição para especificar
a linguagem reconhecida por um autômato.
Dado um autômato $cal(A)=(Σ,Q,q_0,F,δ)$,
dizemos que ele reconhece a palavra $w$ se existe um caminho $p$
que leva do estado inicial para um final, passando por $w$. Isto é:
- $lab(p) = w$
- $ini(p) ∈ S$
- $fin(p) ∈ F$
- $ars(p) ⊆ δ$

= Semântica operacional big-step

#let bigstep(X, w) = $#X ⇓ #w$
#let step(X, a, Y) = $#X attach(→, t:#a) #Y$

A especificação formal baseada em caminhos tem a vantagem
de que é fácil visualizar os caminhos,
porém pode ser inconveniente na hora de escrever provas matemáticas.
A raiz do problema é que a estrutura de dados do caminho não
tem nada que impeça a criação de um caminho espúrio,
que não tem nada a ver com o autômato.
O resultado disso é que a especificação, além do caminho em si,
também usa uma série de predicados baseados em $lab$, $ini$, $fin$, e $ars$.

Nesta seção vamos apresentar uma formulação alternativa da semântica de um autômato,
que especifica diretamente o que é um caminho adequado. 
A relação $bigstep(q, w)$ codifica que existe um caminho adequado
que leva de $q$ para um estado final, passando por $w$.

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
            $(X,a,Y) ∈ δ$,
            $bigstep(Y, v)$,
        )
    ),
)

A maneira de ler esta notação de _dedução natural_
é que a parte acima da barra lista as premissas,
e a parte de baixo mostra a conclusão.
Por extenso:

1. Se $X$ é um estado final, então ele reconhece a palavra vazia
2. Se existe uma aresta de $step(X,a,Y)$,
   e $Y$ reconhece $v$, então $X$ reconhece $a v$.
3. Estados só reconhecem palavras descritas pelas regras acima.

#definition("Linguagem aceita por um AFD")[$L(cal(A)) = {w | bigstep(q_0, w)}$]


#lemma[
    $L_(⇓)(cal(A)) ⊆ L_(P)(cal(A))$. Isto é, se $bigstep(X, w)$, então existe $p$ com
    - $ini(p) = X$,
    - $fin(p) ∈ F$,
    - $lab(p) = ε$,
    - $ars(p) = δ$.
]
#proof[
    
    Basicamente, temos que apresentar um procedimento que recebe uma
    evidência de $w ∈ L_(⇓)(cal(A))$ e produz uma evidência de $w ∈ L_(P)(cal(A))$.
    A prova é por indução estrutural na evidência $bigstep(X, w)$,
    e tem a cara de uma função recursiva que recebe a derivação de $bigstep(X, w)$,
    e deve produzir um caminho $P$, junto com evidência de que $P$ é um caminho
    apropriado, que reconhece $w$.

    / Caso base: $(X ∈ F) / bigstep(X, ε)$

    A evidência que recebemos contém uma sub-evidência de que $X ∈ F$.
    Poderemos usar este fato mais em frente.
    (By the way, este empacotamento de sub-evidências é o principal atrativo)

    Cada caso tem que apresentar um caminho e provar que ele é adequado.
    Para o caso base escolhemos $P=pathnil(X)$.
    Continuamos aplicando as definições de $ini, fin, lab, ars$:

    $
    ini(pathnil(X)) &= X \
    fin(pathnil(X)) &= X \
    lab(pathnil(X)) &= ε  \
    ars(pathnil(X)) &= {} \
    $

    Como o conjunto vazio está contido em qualquer outro conjunto, temos $ars(P) ⊆ δ$.
    Além disso, vimos antes que $X ∈ F$ e portanto $fin(P) ⊆ F$.
    Portanto, $P$ é um caminho que leva de $X$ a um estado final, lendo a string $w=ε$.
    
    / Caso indutivo: $((X,a,Y) ∈ δ; bigstep(Y, w')) / bigstep(X, a · w')$

    Desta vez, as sub-evidências que recevemos são uma evidência de que
    a aresta $(X,a,Y)$ pertence ao autômato, e que $bigstep(Y, w')$.
    Aplicando a hipótese de indução em $bigstep(Y, w')$,
    como se fosse uma chamada recursiva,
    concluimos que existe um caminho $p'$ que reconhece $w'$ a partir de $Y$:
    $ini(p') = Y$, 
    $fin(p') ∈ F$,
    $lab(p') = w'$,
    $ars(p') = δ$.

    Agora temos que usar essas peças
    para construir um caminho que reconhece $a · w'$ saíndo de arr($X$).
    Vamos escolher o caminho $P=pathcons(X,a, p')$. Temos
    $
    ini(pathcons(X,a, p')) &= X \
    fin(pathcons(X,a, p')) &= fin(p')\
    lab(pathcons(X,a, p')) &= a •lab(p')\
    ars(pathcons(X,a, p')) &= {(X,a,Y)} ∪ ars(p')\
    $

    Juntando isso com a hipótese de indução,
    podemos concluir que $fin(P) = fin(P') ⊆ F$,
    e que $lab(P) = a · w'$.
    Por último, $ars(P) ⊆ δ$ segue de $(X,a,Y) ∈ δ$ e de $ars(p') ⊆ δ$.
]

#lemma[
    $L_(P)(cal(A)) ⊆ L_(⇓)(cal(A))$.
    Isto é, $p$ é um caminho que reconhece $w=lab(P)$, saíndo de $X=ini(P)$,
    então $bigstep(ini(P), lab(P))$.
]
#proof[
    Desta vez a prova é por indução no caminho $P$.
    
    / Caso base: $P=pathnil(X)$

    Por definição, $ini(pathnil(X)) = fin(pathnil(X)) = X$ e $lab(pathnil(X))=ε$.
    Pela hipótese podemos assumir $ini(P)∈F$,
    que é a premissa necessária para construir evidência de $bigstep(X, ε)$.

    #proof-tree(
        rule(
            $bigstep(X, ε)$,
            //----
            $X ∈ F$,
        )
    )

    / Caso indutivo: $P=pathcons(X, a, P')$

    Pela nossa premissa, sabemos que $fin(P) ∈ F$, e $ars(P) ⊆ δ$.
    Aplicando as definições, temos
    $ini(P) = X$,
    $fin(P) = fin(P')$,
    $lab(P) = a · lab(P')$,
    $ars(P) = {(X, a, ini(P'))} ∪ ars(P')$.
    Com isso, queremos obter evidência de $bigstep(X, a · lab(P'))$:

    #proof-tree(
        rule(
            $bigstep(X, a · lab(P'))$,
            //----
            $(X, a, ini(P')) ∈ δ$,
            $bigstep(ini(P'), lab(P'))$,
        )
    )


    Para tal precisamos de uma evidência de que $bigstep(ini(P'), lab(P'))$.
    Dá vontade de aplicar a hipótese de indução sobre $P'$, porém ainda não podemos!
    A nossa premissa nos premite assumir que $P$ reconhece $w$,
    mas não diz nada sobre $P'$.
    Antes de aplicar a hipótese de indução,
    temos que reconstruir a evidência de que $P'$ é um caminho adequado.
    Isto é, $fin(P') ∈ F$ e $ars(P') ⊆ δ$.
    (Esta complicação é exatamente o motivo pelo qual introduzimos a relação $⇓$.
     A vida fica mais tranquilo quando a evidência contém as sub-evidências).

    A primeira condição segue da premissa $fin(P) ∈ F$, junto com o $fin(P) = fin(P')$.
    A segunda condição segue da premissa $ars(P) ⊆ δ$,
    que também permite concluir  $(X, a, ini(P')) ∈ δ$.

    Chegamos na reta final. Aplicando a hipótese de indução em $P'$,
    obtemos uma evidência de que $bigstep(ini(P'), lab(P'))$,
    e com isso podemos construir a evidência de que $bigstep(ini(P), lab(P))$.
]
   
= Semântica operacional small-step

#let dmult = $attach(=>, tr:*)$

Uma semântica baseada na ideia de derivações de gramáticas.

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
            $(X,a,Y) ∈ δ$,
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

Precisamos também de uma relação que capture a ideia de "zero ou mais passos".

$
  " E" dmult "abbb"
$

Esta relação é o fecho reflexivo e transitivo de $=>$.

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
            $X dmult Y$,
            //--------------
            $X => Y$,
        )
    ),

    proof-tree(
        rule(
            $X dmult Z$,
            //--------------
            $X dmult Y$,
            $Y dmult Z$,
        )
    ),
)

Outra maneira:

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


Obs.: 
A semântica baseada em $⇓$ é o que chamamos de _big step_.
Ela relaciona um estado diretamente com o resultado final, que é uma string de $Σ^*$.
Já a semântica com $=>$ é _small step_.
A relação captura um passo de cada vez.
Repare que o lado direito da seta pode conter nomes de estado,
além de caracteres do alfabeto $Σ$.

Estas duas abordagens tem seus prós e contras.
Semânticas big-step comumente resultam em provas mais simples,
pois a definição indutiva da relação tem menos regras.
A semântica small-step tem a vantagem da notação ser mais horizontal.
Também está mais bem equipadas para lidar com loops/caminhos infinitos.
(Nós combinamos  de deixar as strings infinitas de fora das nossas linguagens,
mas essa questão do loop infinito aparece comumente em outros contextos.)

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


= Lema de Arden

#lemma[
    $A^*B$ é solução da equação $X = A X ∪ B$.
] <thm:arden-solution>
#proof[
    $
    & A X ∪ B \
    & = A · (A^*B) ∪ B \
    & = A · (union.big_(i=0)^(∞) A^i B) ∪ B \
    & = (union.big_(i=1)^(∞) A^i B) ∪ A^0 B \
    & = (union.big_(i=0)^(∞) A^i B) \
    & = X
    $
]


Agora resta mostrar que $A^*B$ é a menor solução.
Isto é, qualquer solução $X$ é superconjunto de $A^*B$.
Um argumento intuitivo é que
se substituirmos $X$ por $A X ∪ B$ sucessivamente,
os termos de $A^*B$ vão aparecendo: $A^0 B$, $A^1 B$, $A^2 B$, $...$

$
                                  X &= A^0 X \
                      A^0 (A X ∪ B) &= A^1 X ∪ A^0 B \
               A^1(A X ∪ B) ∪ A^0 B &=  A^2 X ∪ A^1 B ∪ A^0 B\
      A^2 (A X ∪ B) ∪ A^1 B ∪ A^0 B &=  A^3 X ∪ A^2 B ∪ A^1 B ∪ A^0 B\
                                    &...
$

A prova formal é por indução no número de repetições da estrela de Kleene.

#lemma[
    Se $A X ∪ B ⊆ X $ então $A^*B ⊆ X$.
] <thm:arden-least>
#proof[
    O nosso objetivo equivale a dizer que
    para todo $n$, $A^n B ⊆ X$.
    Vamos provar isto por indução em $n$

    Caso base: $n=0$

    $A^0 B = B ⊆ A X ∪ B ⊆ X$

    Caso indutivo: $n ≥ 1$

    Pela hipótese de indução, podemos assumir $A^(n-1) B ⊆ X$.
    Por monotonicidade da concatenação, $A A^(n-1) B ⊆ A X$.
    Portanto, $A^n B ⊆ A X ⊆ A X ∪ B ⊆ X$.
]

Finalmente, provamos o lema de Arden propriamente dito.

#theorem("Lema de Arden")[
    $A^*B$ é a menor solução de $X = A X ∪ B$.
] <thm:arden>
#proof[
    O @thm:arden-solution nos diz que $A^*B$ é solução,
    e o @thm:arden-least nos diz que todas as soluções contém $A^*B$.
]

No teorema @thm:arden, tivemos um bom trabalho para especificar
que buscamos a menor solução, e não meramente uma solução qualquer.
O que justifica este esforço? Em que casos existem outras soluções
além da menor solução $A^*B$? Um exemplo é a equação

$
X = X ∪ {a}
$

A menor solução é o conjunto ${a}$.
No entanto, também são soluções todos os superconjuntos de ${a}$.
A maior destas soluções é $Σ&^*$, a linguagem que contém todas as palavras.
A culpa disso está no $X=X$ da equação,
que ocorre quando o conjunto $A$ contém a palavra vazia.
(O que corresponde a um loop vazio no autômato)

Como vimos anteriormente, a menor solução 
advem dos termos $A^i B$ daqueles somatórios.
Intuitivamente, para obter uma solução diferente de $A^* B$
esta solução deve conter strings oriundas do termo $A^n X$.

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
    X & ⊆ A^n X ∪ (union.big_(i=0)^(n-1) A^i B) \
      & ⊆ A^n (A X ∪ B)  ∪ (union.big_(i=0)^(n-1) A^i B) \
      & = A^(n+1) X ∪ A^n B ∪ (union.big_(i=0)^(n-1) A^i B) \
      & = A^(n+1) X ∪ (union.big_(i=0)^n A^i B) \
    $
]

Usamos este lema para mostrar que, se $A$ não contém a palavra vazia,
então todas as soluções do sistema estão dentro de $A^*B$.

#lemma[
    Se $ε ∉ A$, e $X ⊆ A X ∪ B$,
    então $X ⊆ A^*B$.
] <thm:arden-greatest>

#proof[
   Seja $w$ uma palavra de $X$,
   e seja $abs(w)$ o seu comprimento.
   Pelo @thm:arden-greatest, deduzimos que $w ∈  A^(abs(w)+1) X ∪ (union.big_(i=0)^(abs(w)) A^i B)$.
   Mas repare que $ε ∉ A$.
   Portanto, $A$ só contém palavras com comprimento maior ou igual a 1,
   e $A^(abs(w)+1) X$ só contém palavras com comprimento pelo menos $abs(w)+1$.
   Assim, não é possível que $w$ pertença a $A^(abs(w)+1) X$.
   Necessariamente temos $w ∈ (union.big_(i=0)^(abs(w)) A^i B) ⊆ A^* B$.
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
equações como $X = a X$ permitiriam soluções infinitas como $a a a ...$.
Nestas notas de aula, nós não permitimos e nem permitiremos estas strings infinitas.
No entanto, eu queria deixar registrado que existem sim situações
em que falar de strings infinitas faz sentido.
Essa escolha levaria a um teoria alternativa,
que trabalharia com maiores pontos fixos ao invés de menores pontos fixos,
e provas por co-indução ao invés de por indução.

= Pontos Fixos

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
Também nos permite usar a notação $lfp(f)$ para se referir ao menor ponto fixo.

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


