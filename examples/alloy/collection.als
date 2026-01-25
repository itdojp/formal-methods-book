module collection

sig Elem {}

sig Collection {
  items: set Elem
}

pred NonEmpty(c: Collection) {
  some c.items
}

run { some c: Collection | NonEmpty[c] } for 3
