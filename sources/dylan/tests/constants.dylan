Module:       dylan-test-suite
Synopsis:     Dylan test suite
Author:       Andy Armstrong
Copyright:    Original Code is Copyright (c) 1995-2004 Functional Objects, Inc.
              All rights reserved.
License:      See License.txt in this distribution for details.
Warranty:     Distributed WITHOUT WARRANTY OF ANY KIND

// Helper function to force evaluation at run-time,
// instead of compile-time.
define not-inline function run-time (x)
  x
end function run-time;

/// Constant testing

define dylan constant-test $permanent-hash-state ()
  //---*** Fill this in...
end constant-test $permanent-hash-state;

define dylan-extensions constant-test $minimum-integer ()
  //---*** Add some more tests here...
  check-condition("$minimum-integer - 1 overflows",
		  <error>,
		  $minimum-integer - run-time(1))
end constant-test $minimum-integer;

define dylan-extensions constant-test $maximum-integer ()
  //---*** Add some more tests here...
  check-condition("$maximum-integer + 1 overflows",
		  <error>,
		  $maximum-integer + run-time(1))
end constant-test $maximum-integer;
