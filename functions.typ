#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/ctheorems:1.1.3": *

#let theorem    = thmplain("teorema", "Teorema", titlefmt: strong)
#let lemma      = thmplain("lema", "Lema", titlefmt: strong)
#let definition = thmplain("definição", "Definição", titlefmt: strong)
#let corollary  = thmplain("corolário", "Corolário", base: "theorem", titlefmt: strong)
#let example    = thmplain("examplo", "Examplo").with(numbering: none)
#let proof      = thmproof("prova", "Prova")


#let implies   = $==>$
#let impliedby = $<==$
#let iff       = $<==>$