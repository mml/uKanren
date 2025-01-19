# vim:set fdm=marker fdc=4: # {{{1
use warnings;
use strict;
use diagnostics;

use feature qw(isa signatures);

package MicroKanren; # {{{1

require Exporter;
our @ISA = qw(Exporter);
our @EXPORT_OK = qw(
  NIL Zzz
  call_fresh car cdr cons empty_state disj equ goal mbind mplus nullp pairp
  pull var
  varp
  walk
);
our @EXPORT = @EXPORT_OK;

use constant VAR_PACKAGE => 'MicroKanren::Var';
use constant PAIR_PACKAGE => 'MicroKanren::Pair';

### Variables {{{1
sub var($c) { bless \$c, VAR_PACKAGE }
sub varp($x) { VAR_PACKAGE eq ref $x }
sub var_eq($x1, $x2) {
  varp($x1) and varp($x2) and ($$x1 == $$x2);
}

### Pairs and substitutions {{{1
use constant NIL => [];
sub cons($a, $d) { bless [$a, $d], PAIR_PACKAGE }
sub pairp($x) { ref $x eq PAIR_PACKAGE }
sub nullp($x) { ref $x and $x == NIL }
sub car($x) { $x->[0] }
sub cdr($x) { $x->[1] }
sub ext_s($x, $v, $s) { cons(cons($x, $v), $s) }
sub empty_s() { NIL }
sub assp :prototype(&$) ($f, $l) {
  for(my $l = $l; not nullp($l); $l = cdr($l)) {
    {
      my $a = car($l);
      local $_ = car($a);
      return $a if ($f->($_));
    }
  }

  return 0;
}
sub eqv($x, $y) {
  (ref $x and ref $y and $x == $y) or $x eq $y;
}

### Monad {{{1
use constant MZERO => NIL;
sub codep($x) { 'CODE' eq ref $x }
sub unit($s_c) { cons($s_c, MZERO) }
sub mplus($stream1, $stream2) {
  return $stream2 if nullp($stream1);
  return sub { mplus($stream2, $stream1->()) } if codep($stream1);
  cons(car($stream1), mplus(cdr($stream1), $stream2));
}
sub mbind($stream, $goal) {
  return MZERO if nullp($stream);
  return sub { mbind($stream->(), $goal) } if codep($stream);
  mplus($goal->(car($stream)), mbind(cdr($stream), $goal));
}

### Unification {{{1
sub walk($u, $s) {
  while (varp($u)) {
    my $pr = assp { var_eq($u, $_) } $s;
    if ($pr) { $u = cdr($pr) }
    else { last }
  }
  return $u;
}

sub unify($u, $v, $s) {
  $u = walk($u, $s);
  $v = walk($v, $s);
  return $s if var_eq($u, $v);
  return ext_s($u, $v, $s) if varp($u);
  return ext_s($v, $u, $s) if varp($v);
  if (pairp($u) and pairp($v)) {
    my $s = unify(car($u), car($v), $s);
    return $s || unify(cdr($u), cdr($v), $s);
  }
  return eqv($u, $v) && $s;
}

### Goal Constructors {{{1

sub goal :prototype(&) ($f) {
  MicroKanren::Goal->new($f);
}

sub Zzz :prototype(&) ($thunk) {
  goal sub($s_c) { sub { $thunk->()->($s_c) } }
}

sub equ($u, $v) {
  goal sub ($s_c) {
    my $s = unify($u, $v, car($s_c));
    if ($s) {
      return unit(cons($s, cdr($s_c)));
    } else {
      return MZERO;
    }
  }
}

sub call_fresh($n, $f = undef) {
  if (!defined $f) {
    $f = $n;
    $n = 1;
  }
  goal sub($s_c) {
    my $c = cdr($s_c);
    my @v;
    push @v, var($c++) while $n--;
    $f->(@v)->(cons(car($s_c), $c));
  }
}

sub disj { goto &MicroKanren::Goal::disj }
sub conj { goto &MicroKanren::Goal::conj }

### UI Affordances {{{1
use constant EMPTY_S_C => cons(empty_s(), 0);
sub empty_state() { EMPTY_S_C }
sub pull($stream) {
  $stream = $stream->() while codep($stream);
  return $stream;
}
package MicroKanren::Goal; #{{{1
use XXX;

import MicroKanren qw(Zzz mbind mplus);

# See perlop for precedence and associativity.
use overload
    '&' => \&conj_op,
    '|' => \&disj_op;

sub new($class, $code) {
  bless $code, $class;
}

sub disj($g1, $g2) {
  MicroKanren::Goal->new(
    sub($s_c) { mplus($g1->($s_c), $g2->($s_c)) }
  )
}

sub conj($g1, $g2) {
  MicroKanren::Goal->new(
    sub($s_c) { mbind($g1->($s_c), $g2) }
  )
}

sub disj_op($g1, $g2, $swap, $nomethod = undef, $bitwise = undef) {
  die if $swap;
  #YYY [$g1, '|', $g2];
  MicroKanren::Goal::Disjunction->new($g1, $g2);
}

sub conj_op($g1, $g2, $swap, $nomethod = undef, $bitwise = undef) {
  die if $swap;
  #YYY [$g1, '&', $g2];
  conj($g1, $g2);
}

package MicroKanren::Goal::Disjunction; #{{{2
use XXX;

our @ISA = qw(MicroKanren::Goal);

import MicroKanren qw(Zzz);

use overload
    '|' => \&disj_op;

sub new($class, $g1, $g2) {
  my $x = MicroKanren::Goal::disj(Zzz(sub {$g1}), Zzz(sub {$g2}));
  bless $x, $class;
}

sub disj_op($g1, $g2, $swap, $nomethod = undef, $bitwise = undef) {
  die if $swap;
  my $x;
  if ($g2 isa MicroKanren::Goal::Disjunction) {
    $x = MicroKanren::Goal::disj($g1, $g2);
  } else {
    $x = MicroKanren::Goal::disj($g1, Zzz(sub {$g2}));
  }
  bless $x, __PACKAGE__;
}

1;
