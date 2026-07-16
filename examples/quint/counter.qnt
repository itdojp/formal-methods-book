module counter {
  var count: int

  action init = count' = 0

  action increment = all {
    count < 3,
    count' = count + 1,
  }

  val NonNegative = count >= 0
  val WithinBound = count <= 3

  run initTest = init.expect(and {
    count == 0,
    NonNegative,
    WithinBound,
  })

  run incrementTest = init
    .then(increment)
    .expect(and {
      count == 1,
      NonNegative,
      WithinBound,
    })
}
