import Mathlib

/-!
# Project Euler Problem 19: Counting Sundays

You are given the following information, but you may prefer to do some research
for yourself.

1 Jan 1900 was a Monday.
Thirty days has September, April, June and November.
All the rest have thirty-one,
Saving February alone, which has twenty-eight, rain or shine.
And on leap years, twenty-nine.

A leap year occurs on any year evenly divisible by 4, but not on a century
unless it is divisible by 400.

How many Sundays fell on the first of the month during the twentieth century
(1 Jan 1901 to 31 Dec 2000)?

Answer: 171
-/
namespace ProjectEuler19

/-- Days in each month (non-leap year). -/
def days_in_month (month : ℕ) : ℕ :=
  match month with
  | 1 => 31  | 2 => 28  | 3 => 31
  | 4 => 30  | 5 => 31  | 6 => 30
  | 7 => 31  | 8 => 31  | 9 => 30
  | 10 => 31 | 11 => 30 | 12 => 31
  | _ => 0

/-- Is a given year a leap year? -/
def is_leap (year : ℕ) : Bool :=
  year % 400 = 0 ∨ (year % 4 = 0 ∧ year % 100 ≠ 0)

/-- Days in a given month of a given year. -/
def days_in (year month : ℕ) : ℕ :=
  if month = 2 ∧ is_leap year then 29 else days_in_month month

/-- Days between 1 Jan 1900 and the start of a given year-month. -/
def days_since_1900 (year month : ℕ) : ℕ :=
  (Finset.Icc 1900 (year - 1)).sum (λ y => if is_leap y then 366 else 365) +
  (Finset.Icc 1 (month - 1)).sum (λ m => days_in year m)

/-- Day of week: 0=Monday, 1=Tuesday, ..., 6=Sunday. -/
def day_of_week (year month : ℕ) : ℕ :=
  days_since_1900 year month % 7

/-- Count of months from 1901-1900 where the 1st was a Sunday (day_of_week = 6). -/
def count_sundays : ℕ :=
  (Finset.Icc 1901 2000).sum (λ y =>
    (Finset.Icc 1 12).sum (λ m =>
      if day_of_week y m = 6 then 1 else 0))

theorem answer_correct : count_sundays = 171 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler19
