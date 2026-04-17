#include "verification_stdlib.h"
#include "hull.h"

#include <stdio.h>
#include <stdlib.h>

int unique_points(Point *pts, int n);
int graham_scan(Point *pts, int n, Point *hull);

int main(void) {
    int t;
    if (scanf("%d", &t) != 1) return 0;

    printf("%d\n", t);

    for (int tc = 0; tc < t; tc++) {
        int n;
        if (scanf("%d", &n) != 1) return 0;

        /* Safe malloc? */
        Point *pts = (Point *)malloc((size_t)n * sizeof(Point));
        Point *hull = (Point *)malloc((size_t)n * sizeof(Point));
        // if (pts == NULL || hull == NULL) {
        //     free(pts);
        //     free(hull);
        //     return 0;
        // }

        for (int i = 0; i < n; i++) {
            if (scanf("%lld %lld", &pts[i].x, &pts[i].y) != 2) {
                free(pts);
                free(hull);
                return 0;
            }
        }

        int m_in = unique_points(pts, n);
        int m_hull = graham_scan(pts, m_in, hull);

        int out_n = m_hull + 1;
        printf("%d\n", out_n);
        for (int i = 0; i < m_hull; i++) {
            printf("%lld %lld\n", hull[i].x, hull[i].y);
        }
        printf("%lld %lld\n", hull[0].x, hull[0].y);

        if (tc + 1 < t) {
            int sep;
            if (scanf("%d", &sep) != 1) {
                free(pts);
                free(hull);
                return 0;
            }
            printf("-1\n");
        }

        free(pts);
        free(hull);
    }

    return 0;
}
