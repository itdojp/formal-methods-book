module ch04_university_enrollment

sig Course {}

sig Student {
  enrollment: set Course
}

fact MaxCourses {
  all s: Student | #(s.enrollment) <= 5
}

run { some s: Student | some s.enrollment } for 3 Student, 5 Course

