package pkg

// fails: comparing two incomparable multisets
//:: ExpectedOutput(type_error)
ensures m == n
func foo(ghost m mset[int]) (ghost n mset[bool]) {
}
