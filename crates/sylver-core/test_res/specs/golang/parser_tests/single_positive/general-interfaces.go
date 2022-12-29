package main

import "fmt"

type hello1 interface {
	int
}

type Ordered interface {
    ~int | ~int8 | ~int16
}

type hello2 interface {
	~int
}

type hello3 interface {
	~int
	String() string
}

type hello4 interface {
	int
	string
}