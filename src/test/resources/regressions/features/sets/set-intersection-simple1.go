package pkg

func example1(ghost s set[int], ghost t set[int]) {
  ghost u := s intersection t
}

func example2() {
  assert set[bool] { } intersection set[bool] { } == set[bool] { }
  assert set[int] { 1, 2 } intersection set[int] { 2, 3 } == set[int] { 2 }
  assert set[int] { 1, 2 } intersection set[int] { 3, 4 } == set[int] { }
}

func example3() {
  assert set[int] { 1, 2, 3 } intersection set[int] { 1, 2 } intersection set[int] { 2 } == set[int] { 2 }
}

func example4(ghost s set[int], ghost t set[int], ghost u set[int]) {
  assert (s intersection t) intersection u == s intersection (t intersection u)
  assert s union (t intersection u) == (s union t) intersection (s union u)
  assert s intersection (t union u) == (s intersection t) union (s intersection u)
}

ensures t == s intersection set[int] { 2, 1 }
func example5(ghost s set[int]) (ghost t set[int]) {
  t = s intersection set[int] { 1, 2 }
}

func example6(ghost s set[int]) {
  assert s intersection s == s
  assert s intersection set[int] { } == set[int] { }
}

func example7(ghost s set[int], ghost t set[int]) {
  assert s intersection t == t intersection s
}

