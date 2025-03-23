#let implies   = $==>$
#let impliedby = $<==$
#let iff       = $<==>$

#let rev(x) = $#x ^R$

#let fix(f) = $μ#f$
#let lam(x, e) = $⟨#x ↦ #e⟩$
#let fixl(x, e) = $fix(lam(#x,#e))$


// Produces a calculational proof that looks like this:
//
// $
//    &    && formula \
//    & op && hint    \ 
//    &    && formula \
//    & op && hint    \
//    &    && formula \
// $
#let calculation(
  item-spacing: 0.5em,
  hint-spacing: 1.5em,
  ..rows
) = {
  for (i, row) in rows.pos().enumerate() {
    let col1
    let col2
    if calc.rem(i, 2) == 0 { 
      let formula = row.at(0)
      col1 = none      
      col2 = { h(item-spacing); formula }
      
    } else {
      let op   = row.at(0)
      let hint = row.at(1, default:none)
      col1 = op
      col2 = if hint != none {
        { h(hint-spacing); "{"; h(0.5em); hint; h(0.5em); "}" }
      } else {
        none 
      }
    }

    $ & #col1 && #col2 \ $
  }
}