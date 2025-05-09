#include "predicates.c"

#include <math.h>

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
  for (int i = 0; i < 17; ++i ) {
    p0.x = nextafter(p0.x, INFINITY);
    p0.y = nextafter(p0.y, INFINITY);
  }

  exactinit();
  orient2d(p1.v, p0.v, p2.v);
}
