module ch04_leader_election

sig Node {
  id: one Int,
  leader: Node lone -> Time,
  alive: set Time
}

sig Message {
  from: one Node,
  to: one Node,
  content: one MessageType,
  timestamp: one Time
}

abstract sig MessageType {}
one sig Election, OK, Coordinator extends MessageType {}

sig Time {
  next: lone Time
}

fact uniqueIds {
  all disj n1, n2: Node | n1.id != n2.id
}

fact initialState {
  some first: Time | no first.~next and
    all n: Node |
      no n.leader.first and
      first in n.alive
}

pred startElection[n: Node, t: Time] {
  t in n.alive
  no n.leader.t
  all higher: Node | higher.id > n.id and t in higher.alive implies
    some m: Message |
      m.from = n and
      m.to = higher and
      m.content = Election and
      m.timestamp = t
}

pred respondToElection[receiver: Node, sender: Node, t: Time] {
  t in receiver.alive
  receiver.id > sender.id
  some m: Message |
    m.from = receiver and
    m.to = sender and
    m.content = OK and
    m.timestamp = t
  startElection[receiver, t]
}

pred becomeLeader[n: Node, t, tNext: Time] {
  tNext = t.next
  t in n.alive
  no m: Message |
    m.to = n and
    m.content = OK and
    m.timestamp = t
  n.leader.tNext = n
  all lower: Node | lower.id < n.id and t in lower.alive implies
    some m: Message |
      m.from = n and
      m.to = lower and
      m.content = Coordinator and
      m.timestamp = tNext
}

assert leaderUniqueness {
  all t: Time | lone n: Node | n.leader.t = n
}

assert leaderIsAlive {
  all n: Node, t: Time |
    n.leader.t = n implies t in n.alive
}

assert highestIdWins {
  all t: Time, n: Node |
    n.leader.t = n implies
      no higher: Node | higher.id > n.id and t in higher.alive
}

check leaderUniqueness for 5 Node, 10 Message, 8 Time
check leaderIsAlive for 5 Node, 10 Message, 8 Time
check highestIdWins for 5 Node, 10 Message, 8 Time
