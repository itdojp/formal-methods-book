module queue

sig Elem {}

sig Queue {
  items: set Elem
}

pred NonEmpty(q: Queue) {
  some q.items
}

run { some q: Queue | NonEmpty(q) } for 3
