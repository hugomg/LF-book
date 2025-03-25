#import "functions.typ": *

#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/ctheorems:1.1.3": *

// TODO shared counters don't work (?)
#let theorem    = thmplain("theorem", "Teorema", titlefmt: strong)
#let lemma      = thmplain("lemma", "Lema", titlefmt: strong)
#let definition = thmplain("definition", "Definição", titlefmt: strong)
#let corollary  = thmplain("corollary", "Corolário",  titlefmt: strong)
#let example    = thmplain("examplo", "Examplo").with(numbering: none)
#let proof      = thmproof("prova", "Prova")
#let exercise   = thmplain("exercise", "Exercício",  titlefmt: strong).with(base_level: 1)

#show: thmrules.with(qed-symbol: $square$)

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
    size:11pt,
    lang: "pt"
)

#set heading(numbering: "1.")

#show raw: set text(font: "New Computer Modern Mono")

#show heading: set block(above: 1.4em, below: 1em)
#show heading.where(depth:1): body => { pagebreak(weak: true); body}

// Make ":" be punctuation by default.
// We use it for type annotations, forall, exists.
#show sym.colon: it => math.class("punctuation", it)



//=================================================


= Autômatos e Linguagens

Autômatos finitos são um modelo de um processo computacional.
Além das aplicações diretas para processamento de texto
e especificação de sistemas, eles também são o fundamento
para modelos mais complexos, para computação em geral.

Alguns exemplos de perguntas que temos interesse em estudar:

- Para quais entradas um certo algoritmo produz a saída desejada?
- Duas implementações diferentes do mesmo algoritmo são equivalentes?
- Existem problemas que não podem ser solucionados pelo nosso modelo computacional?
- Qual é o impacto de introduzir não-determinismo no nosso modelo?

Vamos partir para um exemplo!


Esse autômato descreve uma disputa de pênaltis entre Brasil e Argentina.
Já estamos nas cobranças alternadas, e a Argentina bate primeiro.
Começamos no estado inicial E.
A primeira linha acontece se a Argentina fizer o gol (a).
Avançamos para o estado A, com vantagem para a Argentina,
e esperamos a cobrança do Brasil.
Se o Brasil também marcar (b),
nós voltamos para a estaca zero;
se o Brasil errar (x), a Argentina vence (F1).
A segunda linha acontece se a argentina errar a cobrança (x),
caso em que avançamos do estado E para o B.
Desta vez, se o Brasil acertar a sua cobrança (b) ele ganha (F2),
mas se errar (x) então voltamos ao início.


#figure(
    image("imgs/penalti.dot.svg"),
    caption: [Cobrança de pênaltis entre Brasil e Argentina]
) <img:penaltis1>

Uma cobrança de pênaltis corresponde a um caminho no grafo,
que sai do estado inicial e termina em algum dos estados finais.
Representamos este caminho pela palavra que ele percorre,
juntando as letras de cada aresta percorrida.
Em ordem alfabética, as seguintes cobranças de pênaltis são válidas:

- ax, xb
- abax, abxb, xxax, xxbx
- ababax, ababxb, abxxax, abxxbx, xxabax, xxabxb, xxxxax, xxxxbx
- ...

Este conjunto de palavras caracteriza o comportamento do autômato.
Às vezes é possível construir um outro autômato
que reconhece a mesma linguagem
e portanto se comporta de forma equivalente.
Por exemplo, as palavras do nosso conjunto não distinguem
quem ganhou a disputa, então não faz diferença
se juntarmos os estados F1 e F2 em um estado só.

#figure(
    image("imgs/penalti2.dot.svg"),
    caption: [Como o vencedor não importa, podemos juntar F1 e F2]
) <img:penaltis1>

#image("imgs/penalti2.dot.svg")

Exercício:
As palavras abaixo não são disputas de pênaltis válidas.
Justifique isso tanto pelas regras do futebol,
quanto pelo comportamento do  autômato.

#grid(
    columns: 4,
    gutter: 20pt,
    [a) a x],
    [b) aa],
    [c) axa],
    [d) ba],
)


== Strings

Nossos programas de computador
recebem uma sequência de símbolos
e retornam como saída uma resposta de sim ou não.
Vamos agora discutir quais são as propriedades
esperadas de uma sequência de símbolos.

/ Alfabeto: $Σ$, um conjunto finito de símbolos.
/ String/Palavra: Uma sequência finita de símbolos.
/ String vazia: A letra $ε$ denota a string com zero símbolos.

// NOTA DO PROFESSOR
// Chame atenção para o que é finito ou infinito.
// 
// É essencial que as strings sejam finitas.
// Se permitíssemos strings infinitas, entraríamos no mundo da co-indução.
// 
// Não é tão essencial que o alfabeto seja finito.
// Porém, em autômatos com um número finito de estados
// existe um número finito de grafos de transição entre os estados.
// É sempre possível construir um alfabeto finito equivalente.

O alfabeto pode conter qualquer símbolo.
Nos exemplos é comum usarmos letras de a até z,
mas a princípio pode ser qualquer coisa
inclusive símbolos de pontuação e espaços.

A notação $Σ^*$ se refere ao *conjunto de todas as strings*
que podem ser construídas com os símbolos do alfabeto $Σ$.
É comum escrevermos $w ∈ Σ^*$ para dizer que $w$ é uma string
com símbolos do alfabeto $Σ$.

Algumas operações comuns sobre strings:


/ Concatenação: $"ab" · "cd" = "abcd"$
/ Exponenciação: $("ab")^3 = "ababab"$
/ Comprimento: $|"abcd"| = 4$
/ Reversão: $rev(("abc")) = "cba"$

A operação de concatenação é associativa
e tem como elemento neutro a string vazia.

$
  x · (y · z) = (x · y) · z \ 
  ε · x = x =  x · ε
$

A operação de exponenciação descreve uma concatenação repetida.
Podemos implementar esta repetição com uma definição recursiva.

$
  w ^ 0 &= ε \
  w^(n+1) &= w · w^n
$

Uma vantagem da definição recursiva,
comparada a uma definição com "produtório" ou "três pontinhos"
é que ela facilita provas por indução.

// NOTA DO PROFESSOR
// Achei bom apresentar uma prova fácil logo no início
// para as pessoas já irem se acostumando.

#theorem[
    A concatenação de duas exponenciações obedece
    $ w^n · w^m = w^(n+m) $
]
#proof[
    A prova é por indução em $n$.
    Precisamos mostrar que a equação vale para $n=0$
    e também que, se ela vale para $n$, então vale para $n+1$.

    Caso base: queremos provar $w^0 · w^m = w^(0+m)$.
    
    $ calculation(
        w^0 · w^m ;
        =, #[definição da exponenciação] ;
        ε · w^m ;
        =, #[$ε$ é elemento neutro da concatenação] ;
        w^m ;
        =, #[aritmética] ;
        w^(0+m)
    ) $

    Caso indutivo:
    Assumimos $w^n · w^m = w^(n+m)$
    e queremos $w^(n+1) · w^m = w^(n+m+1)$.
    
    $ calculation(
        w^(n+1) · w^m ;
        =, #[definição da exponenciação] ;
        (w · w^n) · w^m ;
        =, #[concatenação é associativa] ;
        w · (w^n · w^m) ;
        =, #[hipótese de indução] ;
        w · (w^(n+m)) ;
        =, #[definição da exponenciação] ;
        w^(n+m+1)
    ) $
]

// NOTA DO PROFESSOR
// Possível continuação ou exercícios:
// - Definir recursivamente rev e comprimento
// - Provar |ab| = |a|+|b|
// - Provar rev(xy) = rev(y)·rev(x)
// - Provar rev(rev(x)) = x

== Linguagens

Uma #strong[linguagem] é conjunto de strings.
Pudemos descrever o comportamento de um programa
através do conjunto de entradas em que o programa responde "sim".

Linguagens podem ser finitas ou infinitas.
As strings são sempre finitas, mas a linguagem pode conter infinitas strings.
Por exemplo, ${ε, "a", "aa", "aaa", ...}$.

Para representar linguagens,
vamos usar operações que criam linguagens mais complexas
a partir de linguagens mais simples.
Algumas destas operações são operações comuns de conjuntos
e outras são extensões das operações sobre strings.

#grid(
    columns: 2,
    gutter: 25pt,
    align: (horizon+right, horizon+left),
    [/ União:], $A ∪ B = {w | w ∈ A ∨ w ∈ B}$,
    [/ Inserseção:], $A ∩ B = {w | w ∈ A ∧ w ∈ B}$,
    [/ Concatenação:], $A · B = {x · y | x ∈ A ∧ y ∈ B}$,
    [/ Exponenciação:], $A^0 &= {ε}  \ A^(n+1) &= A · A^n$,
    [/ Estrela de Kleene:],
         $A^* &= union.big_(i=0)^∞ A^i = {ε} ∪ A ∪ A^2 ∪ ...$,
    [/ Complemento:], $compl(A) = {w | w ∈ Σ^* ∧ w ∉ A}$,
)

== Expressões regulares

Escrever ${ε}$ e ${a}$ fica reperitivo bem rápido.
É comum abreviarmos para $ε$ e $a$ quando
estiver claro pelo contexto que estamos falando de conjuntos.

Como veremos mais à frente, as linguagens produzidas pelos
autômatos podem ser descritas usando apena
concatenação, união, e estrela.
Estas são as #strong[linguagens regulares].

+ A linguagem vazia $emptyset$ é regular.
+ Para qualquer palavra $w$, a linguagem ${w}$ é regular.
+ Se $A$ e $B$ são regulares, $A · B$ é regular.
+ Se $A$ e $B$ são regulares, $A ∪ B$ é regular.
+ Se $A$ é regular, $A^*$ é regular.
+ Nenhuma outra linguagem é regular.

Exercício: toda linguagem finita é regular.

Propriedades importantes das linguagens regulares:

A concatenação é associativa 
e tem a linguagem ε como elemento neutro.
A concatenação com o conjunto vazio resulta no conjunto vazio.
$
    A · (B · C) = (A · B) · C \
    ε · A = A = A · ε \
    emptyset · A = emptyset  = A · emptyset
$

A união é associativa e comutativa
e tem o conjunto vazio como elemento neutro.
$
    A ∪ (B ∪ C) = (A ∪ B) ∪ C \
    A ∪ B = B ∪ A \
    emptyset ∪ A = A = A ∪ emptyset
$

A união é indepotente
$
    A ∪ A = A
$

Distributividade:
$
  A · (B ∪ C) = A · B ∪ A · C \
  (A ∪ B) · C = A · C ∪ B · C
$

As operações de concatenação e união são monótonas
$
  X ⊆ Y implies A · X ⊆ A · Y \
  X ⊆ Y implies A ∪ X ⊆ A ∪ Y \
$

A concatenação se comporta como uma multiplicação
e a união se comporta como a soma.
O conjunto vazio é similar ao 0
e o conjunto da string de comprimento zero é similar a 1.
No entanto, ao contrário dos números convencionais,
a multiplicação não é comutativa e não existem
operações inversas (subtração e divisão).

A operação $A^*$ descreve a menor solução
da inequação $X ⊇ A X ∪ ε$.
Isto é:

- $A^* ⊇ A A^* ∪ ε$
- $X ≥ A X ∪ ε  implies X ⊇ A^*$

Inclusive podemos ir além e dizer que $A^* = A A^* ∪ ε$ .

$ calculation(
  A^* ⊇ A A^* ∪ ε;
  implies, #[monotonicidade] ;
  A A^* ⊇ A · (A A^* ∪ ε);
  implies, #[monotonicidade] ;
  A A^* ∪ ε ⊇ A · (A A^* ∪ ε) ∪ ε;
  implies, #[$X ≥ A X ∪ ε  implies X ⊇ A^*$] ;
  A A^* ∪ ε ⊇ A^*
) $

// NOTA DO PROFESSOR
// É mais fácil descobrir essa prova de trás pra frente,
// começando pelo final.

== Autômatos


Um autômato finito pode ser descrito
por uma tupla $cal(A) = (Σ, Q, S, F, Δ)$:

/ $Σ$: o alfabeto.
/ $Q$: o conjunto de estados.
/ $S$: o conjunto de estados iniciais.
/ $F$: o conjunto de estados finais.
/ $Δ$: a relação de transição (arestas)

O alfabeto $Σ$ descreve quais caracteres podem aparecer
nas arestas do autômato.

Como é de se esperar,
em um autômato finito o conjunto de estados $Q$ deve ser finito.
Os subconjuntos $S$ e $F$ descrevem os pontos 
de início e de fim dos caminho.

Os caminhos que percorremos no autômato começam
em um estado de $S$ e terminam em algum estado de $F$.

Uma aresta é uma tripla $(Q × Σ^* × Q)$,
com o estado de origem, o rótulo, e o estado de destino.
O conjunto $Δ$ descreve uma relação de transição entre estados.
Pense em uma tabela de um banco de dados relacional, em que as colunas são
o estado de origem, o rótulo da aresta, e o estado de destino.

Um *Autômato Finito Determinístico (AFD)*
é um autômato que podemos testar se uma palavra é reconhecida
sem nunca ter que fazer alguma escolha.
Ele tem um único estado inicial,
e arestas que saem do mesmo estado não compartilham nenhum prefixo.
Em particular, não podem começar com a mesma letra,
e também não existem arestas com rótulo vazio.
Podemos enxegar que a relação de transição tem
uma dependência funcional:
dado o estado atual e a próxima letra da entrada,
há no máximo um estado de destino possível.

No caso geral, temos um *Autômato Finito Não-Determinístico (AFND)*,
que não tem estas restrições.
Eles podem ter mais de um estado inicial
e o conjunto de arestas pode ser uma relação qualquer.
São permitidas arestas com rótulos vazios.
No entanto, para testar se uma palavra é reconhecida,
é preciso testar vários caminhos em paralelo.

VARIAÇÕES: Outros livros podem apresentar autômatos finitos
de uma forma diferente da que eu apresentei.
Todos exigem que o conjunto de estados seja finito,
mas os outros detalhes podem mudar.
Porém em geral é possível adaptar um autômato de um formato para o outro,
de forma que os formalismos são igualmente poderosos.
A seguir eu listo algumas variações comuns.
Você consegue pensar em como adaptar os nossos autômatos para esses formatos?

- O autômato deve ter apenas um estado inicial
- O autômato deve ter apenas um estado final
- Os rótulos não podem ser palavras inteiras.
  Só um símbolo do alfabeto, ou $ε$.
- Em vez da relação de transição (conjunto de arestas),
  há uma função que recebe estado atual e símbolo,
  e retorna um conjunto de estados de destino possíveis.

Exercício:
Sabemos que todo autômato determinístico deve ter um único estado inicial.
Podemos também exigir que tenha um único estado final?
Ou será que existe alguma linguagem que precisa de pelo menos
dois estados finais?

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
            $pathnil(X) hastype X ~> X$,
            //=====
            $X ∈ Q$,
        )
    ),

    proof-tree(
        rule(
            $pathcons(X, a, p) hastype X ~> Z$,
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
+ e nada mais é um caminho.

// NOTA DO PROFESSOR
// A regra 3 é a que proíbe caminhos infinitos.
// Se estivéssemos definindo im tipo co-indutivo, essa parte mudaria.

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
A relação de transição $⊢$ descreve os passos que a máquina executa.
Quando estamos no estado $X$ e o próximo trecho da entrada é $a$,
então se existir uma aresta $X a Y$
nós podemos mudar para o estado $Y$ e consumir o trecho $a$.

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

O autômato aceita todas as palavras aceitas por algum dos estados iniciais.

$
  L(cal(A)) = union.big_(X ∈ S) L(X) = { w | (X, w) asteps (Z, ε) ∧ X∈S ∧ Z∈F }
$

Derivações são tão poderosas quanto caminhos.
É possível escrever um algoritmo que converte de uma para a outra.

$
    "p2d"(#{
        proof-tree(
            rule(
                $pathnil(X) hastype X ~> X$,
                //=====
                $X ∈ Q$,
            )
        )
    }, w) =& (X, w) asteps (X, w) \

    "p2d"(#{
        proof-tree(
            rule(
                $pathcons(X, a, p) hastype X ~> Z$,
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


#strong[Exercício:] prove que a definição com $⇓$
equivale à sua especificação com $asteps$:

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


= Semântica por conjuntos

Semânticas operacionais
exigem que nós rodemos um programa de computador para saber se uma palavra é aceita.
Os detalhes dependem da implementação deste programa de computador.
Até agora já vimos mais de uma versão:
a semântica com  $astep$, a com $=>$, e a com $⇓$.

Uma outra maneira de pensar sobre a semântica do autômato
é especificar quais propriedades nós gostaríamos que fossem verdade
sobre as linguagens reconhecidas por cada estado.
A especificação da relação $⇓$ parece ser um bom começo:

#definition("Especificação da linguagem do autômato")[
#set enum(numbering: "a)")
+ Se $X$ é um estado final, então ele deve reconhecer a palavra vazia
+ Se existe uma aresta $X a Y$
   e $Y$ reconhece $v$, então $X$ deve reconhecer $a v$.
+ Estados só reconhecem palavras que se encaixam nas regras acima.
] <def-viabilidade>


Buscamos atribuir uma linguagem à cada estado, obedecendo estas regras.
As restrições (a) e (b) dizem quando a solução proposta é viável.
Já a regra (c) diz que buscamos a solução mais simples,
na qual as linguagens contém apenas as palavras essenciais
para que a solução seja viável.

== Um exemplo concreto

#image("imgs/aba.dot.svg")

Vamos escrever as restrições para o autômato acima.
Buscamos uma função $L: Q -> Σ^*$ que atribui uma linguagem para cada estado.
As regras (a) e (b) nos dizem que valores de $L(X)$ e $L(Y)$ são viáveis:

+ $ε ∈ L(Y)$
+ $v ∈ L(Y) implies "a" · v ∈ L(X)$
+ $v ∈ L(X) implies "b" · v ∈ L(Y)$

Devemos tomar cuidado para colocar o $X$ e $Y$ no lugar certo.
Vamos ler com calma o que cada uma dessas fórmulas diz.

+ A linguagem de Y deve conter a palavra vazia.
+ Para mostrar que uma palavra começando em "a" pertence à linguagem de X,
    é~suficiente mostrar que o resto desta palavra pertence à linguagem de Y.
+ Para mostrar que uma palavra começando em "b" pertence à linguagem de Y,
    é~suficiente mostrar que o resto desta palavra pertence à linguagem de X.

Uma solução trivialmente viável é
qualquer estado aceitar qualquer palavra.
$
L(X) &= Σ^* \
L(Y) &= Σ^*
$

Uma solução mais esperta é
$
L(X) &= "a"("b" "a"^*) \
L(Y) &= ("b" "a"^*)
$

Vamos conferir que esta solução é viável

+ $ε ∈ ("b" "a")^*$
+ $v ∈ ("b" "a")^* implies "a" · v ∈ "a"("b" "a")^*$
+ $v ∈ "a"("b" "a")^* implies "b" · v ∈ ("b" "a")^*$

Esta solução esperta também é mínima!
Podemos mostrar que qualquer
solução viável contém esta solução como sub-solução.
Isto é, se $L$ é viável então

#[
    #set enum(numbering: "a)")
    + $"a"("b" "a")^* &⊆ L(X)$
    + $("b" "a")^* &⊆ L(Y)$
]

Nossa prova será por indução no comprimento das palavras de $L$.
Para tal, é melhor escrever o enunciado em termos de "$w∈$".
Isto é, para toda palavra $w$ queremos provar

#[
    #set enum(numbering: "a)")
    + $w ∈ "a"("b" "a")^* implies w ∈ L(X)$
    + $w ∈    ("b" "a")^* implies w ∈ L(Y)$
]

A indução tem que tratar três casos:

- $w=ε$.
  A implicação (a) vale vacuosamente pois $ε ∉ "a"("b" "a")^*$.
  A implicação (b) vale pois a hipótese (1) garante que $ε ∈ L(Y)$.

- $w="a" v$.
  Para a implicação (a) queremos mostrar
  que $"a" v ∈ "a"("b" "a")^* implies "a" v ∈ L(X)$.
  Quando $"a"v ∈ "a"("b" "a")^*$, necessariamente $v ∈ ("b" "a")^*$.
  Como $v$ é mais curta que $w$, podemos aplicar a hipótese de indução
  para obter $v ∈ L(Y)$. Pela regra (2) da especificação de factível,
  concluímos $"a" v ∈ L(X)$.

  A implicação (b), $"a" v ∈ ("b" "a"^*) implies "a" v ∈ L(Y)$,
  vale vacuosamente pois palavras que começam com "a"
  nunca casam com $("b" "a")^*$.

- $w="b" v$.
  A prova é análoga à do caso anterior.
  A implicação (a) vale vacuosamente
  e a implicação (b) segue da hipótese de indução junto com a regra (3).


= Sistemas de inequações

Uma vantagem de especificar a semântica do autômato
através de conjuntos é podemos manipulá-los
usando equivalências entre expressões regulares.

Veremos que essa estratégia será útil para demonstrar
que dois autômatos são equivalentes.
A ideia é converter o autômato~$A_1$
para um sistema de restrições~$C_1$
e mostrar que estas restrições equivalem ao sistema~$C_2$,
que por sua vez é o sistema do autômato~$A_2$.



```
A1    A2
|     | 
C1 -- C2

```

== Notação de subconjuntos

Já que vamos trabalhar bastante com estes sistemas
de restrições sobre as linguagens,
vale a pena parar para deixar a notação mais leve.
Para fins ilustrativos usarei novamente o
exemplo do Autômato [?]. Começamos com

+ $ε ∈ L(Y)$
+ $v ∈ L(Y) implies "a" · v ∈ L(X)$
+ $v ∈ L(X) implies "b" · v ∈ L(Y)$


Primeiramente, vou omitir as chamadas $L()$.
Nem o Germán Cano aguenta tanto L.
Daqui pra frente, assuma que se eu escrever um nome de estado
em um contexto que espera um conjunto/linguagem,
na verdade se trata de um $L(X)$.

+ $ε ∈ Y$
+ $v ∈ Y implies "a" · v ∈ X$
+ $v ∈ X implies "b" · v ∈ Y$

Em seguida, podemos trocar as implicações por subconjuntos.
Preste atenção que o $"a"$ e o $"b"$ trocaram de lado,
mas o significado é mesmo de antes.

+ ${ε} ⊆ Y$
+ $"a" · Y ⊆ X$
+ $"b" · X ⊆ Y$

Finalmente, podemos usar união para juntar
todas as inequações do $Y$ em uma regra só.
Também passei a escrever a expressão regular $ε$ no lugar do conjunto ${ε}$.

$
X &⊇ "a" Y \
Y &⊇ "b" X ∪ ε
$

Resumindo, temos uma inequação para cada variável,
com um termo para cada aresta do autômato,
e mais um termo para cada estado final.
No caso geral fica

$
  L(X) ⊇ {ε | X ∈ F} ∪ union.big_(X a Y ∈ Δ) a · L(Y)
$

== Pontos fixos

Quando temos uma equação por variável,
nosso sistema se comporta como uma equação
$accent(X, ->) ⊇ f(accent(X, ->))$,
onde $accent(X, ->)$ é um vetor de linguagens.
Podemos nos aproveitar da rica teoria de pontos fixos.


#definition("Função monótona")[
    Dizemos que uma função $f$ é monótona quando
    $ A ⊆ B implies f(A) ⊆ f(B) $ 
]

Dá para extender esta definição para vetores de linguagens.
Se $A$ e $B$ forem uma lista de linguages (uma para cada estado)
nós comparamos componente a componente.

Temos especial interesse nas soluções
dos sistemas de equações / inequações.

#definition("Ponto prefixo")[$f(x) ⊆ x$]
#definition("Ponto pósfixo")[$x ⊆ f(x)$]
#definition("Ponto fixo")[$f(x) = x$]

Estamos particularmente interessados no menor dos pontos pré-fixos

#definition("Menor ponto prefixo")[
    Dizemos que $fix(f)$ é o menor ponto prefixo de $f$ se
    ele é um ponto prefixo que também é menor ou igual a todos os outros.
    - $f(fix(f)) ⊆ fix(f)$
    - $forall x: f(x) ⊆ x implies fix(f) ⊆ x$
]

#lemma[
    O menor ponto prefixo também é um ponto fixo.
    Portanto, $fix(f)$ é tanto o menor ponto prefixo 
    quanto o menor ponto fixo.
] <thm:lpp-is-lfp>
#proof[
    Já sabemos $f(fix(f)) ⊆ fix(f)$. Resta mostrar $fix(f) ⊆ f(fix(f))$.

    $ calculation(
      f(fix(f)) ⊆ fix(f) ;
      implies, #[$f$ é monótona] ;
      f(f(fix(f))) ⊆ f(fix(f)) ;
      implies, #[$f(fix(f))$ é um ponto prefixo, logo $fix(f)$ é menor] ;
      fix(f) ⊆ f(fix(f))
    ) $
]

Na prática, quando queremos mostrar que algo é um ponto fixo,
basta provar que é prefixo, o que dá menos trabalho.
Por outro lado, se já soubermos mos que algo é um ponto prefixo,
podemos assumir de vez a hipótese mais forte de que é um ponto fixo.

#theorem("Bekić")[
    Um sistema de equações com mais de variável
    pode ser resolvido uma variável de cada vez.

    $
      fixl(vec(x,y), vec(f(x,y), g(x,y))) =
      vec(
        fixl(x, f(x, fixl(y, g(x,y)))),
        fixl(y, g(fixl(x, f(x,y)), y))
      )
    $
]
#proof[
    Winskel (1993) capítulo 10.
]

#corollary("Introdução de equações")[
    Introduzir uma nova equação não altera o resultado das outras equações.
]

#corollary("Remoção de inequações")[
    Remover uma equação não altera o resultado das outras equações,
    caso elas não usem a variável removida.
]

#lemma("Substituição de equação")[
    Substituir uma equação na outra
    não altera a menor solução do sistema.

    #let aa = block[$ x &= f(x,y)      \ y &= g(x,y) $]
    #let bb = block[$ x &= f(x,g(x,y)) \ y &= g(x,y) $]
    $ μ(#aa) = μ(#bb) $
]
#proof[
    Toda solução do sistema de equações da esquerda
    é solução do sistema de equações da direita e vice versa.
    Portanto, o conjunto das soluções é o mesmo
    e a menor solução  também deve ser a mesma.
    
]

#lemma("Substituição de inequação")[
    Substituir uma inequação na outra
    não altera a menor solução do sistema.

    #let aa = block[$ x &⊇ f(x,y)      \ y &⊇ g(x,y) $]
    #let bb = block[$ x &⊇ f(x,g(x,y)) \ y &⊇ g(x,y) $]
    $ μ(#aa) = μ(#bb) $
]
#proof[
    Pelo @thm:lpp-is-lfp,
    a menor solução de um sistema de equações
    também é a menor solução do sistema de inequações.
    Consequentemente, a substituição também vale o sistema de inequações.
]


= Usando os sistemas

#[
    #grid(
        rows: 2,
        columns: 1,
        gutter: 10pt,
        [minimize $X$],
        $
            & X &&⊇ a W ∪ a Z \
            & W &&⊇ b X \
            & Z &&⊇ ε
        $
    )
]

$
&X &&⊇ a W ∪ a Z \
&W &&⊇ b X \
&Z &&⊇ ε
$)


#let insert_alignments(eqn) = {
    show "⊆": $&&⊆$
    show "=": $&&=$
    show "⊇": $&&⊇$
    show linebreak: it => $#it&$
    $ &eqn $
}

#insert_alignments($
X ⊇ a W ∪ a Z \
W ⊇ b X \
Z ⊇ ε
$)

#grid(
    columns:(50%, 50%),
    align:center,

    $
        X &⊇ a W ∪ a Z \
        W &⊇ b X \
        Z &⊇ ε \
    $,
    image("imgs/aba-l.dot.svg"),

    $
        X &⊇ a b X ∪ a \
    $,
    image("imgs/aba-l2.dot.svg"),

    $
        X &⊇ a Y \
        Y &⊇ b X ∪ ε \
    $,
    image("imgs/aba.dot.svg"),

    $
        X &⊇ a Y \
        Y &⊇ b a Y ∪ ε \
    $,
    image("imgs/aba-r2.dot.svg"),

    $
        X &⊇ a Y \
        Y &⊇ b Z ∪ ε \
        W &⊇ a Y \
    $,
    image("imgs/aba-r.dot.svg"),
)

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


