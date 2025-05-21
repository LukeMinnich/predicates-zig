#include "predicates.c"

#include <math.h>
#include <stdio.h>
#include <time.h>

typedef struct
{
  union {
    struct {
      double x;
      double y;
    };
    double v[2];
  };
} Point2D;

int main(void) {
  Point2D p0 = {0.5, 0.5};
  Point2D p1 = {12.0, 12.0};
  Point2D p2 = {24.0, 24.0};
  Point2D p3 = {-12.0, -12.0};

  exactinit();

  // for (int i = 0; i < 16; ++i ) {
  //   p0.x = nextafter(p0.x, INFINITY);
  //   p0.y = nextafter(p0.y, INFINITY);
  // }

  // double value = incircle(p1.v, p2.v, p3.v, p0.v);
  //

  double elapsed_ms = 0.;

  int dim = 256;

  double yd = p0.v[1];
  for (int row = 0; row < dim; ++row) {
    for (int col = 0; col < dim; ++col) {
      double xd = p0.v[0];

      struct timespec t_start = {0}, t_end = {0};
      clock_gettime(CLOCK_MONOTONIC, &t_start);
      Point2D p = {.x = xd, .y = yd };
      volatile double _ = incircle(p1.v, p2.v, p3.v, p.v);
      clock_gettime(CLOCK_MONOTONIC, &t_end);
      elapsed_ms += (  ((double)t_end.tv_sec + t_end.tv_nsec)
                     - ((double)t_start.tv_sec + t_start.tv_nsec))
                  / 1000;

      xd = nextafter(xd, INFINITY);
    }
    yd = nextafter(yd, INFINITY);
  }

  printf("computation time: %.3f\n", elapsed_ms);
}
