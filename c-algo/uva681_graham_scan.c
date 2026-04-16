#include <stdio.h>
#include <stdlib.h>

typedef long long i64;

typedef struct {
    i64 x;
    i64 y;
} Point;

/*@ Extern Coq (Point : *) */

static Point g_pivot;

int cmp_xy(const void *a, const void *b) {
    const Point *pa = (const Point *)a;
    const Point *pb = (const Point *)b;
    if (pa->x < pb->x) return -1;
    if (pa->x > pb->x) return 1;
    if (pa->y < pb->y) return -1;
    if (pa->y > pb->y) return 1;
    return 0;
}

i64 cross(Point a, Point b, Point c) {
    i64 abx = b.x - a.x;
    i64 aby = b.y - a.y;
    i64 acx = c.x - a.x;
    i64 acy = c.y - a.y;
    return abx * acy - aby * acx;
}

i64 dist2(Point a, Point b) {
    i64 dx = a.x - b.x;
    i64 dy = a.y - b.y;
    return dx * dx + dy * dy;
}

int cmp_polar(const void *a, const void *b) {
    const Point *pa = (const Point *)a;
    const Point *pb = (const Point *)b;
    i64 cr = cross(g_pivot, *pa, *pb);
    if (cr > 0) return -1;
    if (cr < 0) return 1;

    i64 da = dist2(g_pivot, *pa);
    i64 db = dist2(g_pivot, *pb);
    if (da < db) return -1;
    if (da > db) return 1;

    if (pa->x < pb->x) return -1;
    if (pa->x > pb->x) return 1;
    if (pa->y < pb->y) return -1;
    if (pa->y > pb->y) return 1;
    return 0;
}

int unique_points(Point *pts, int n) {
    if (n <= 1) return n;
    qsort(pts, (size_t)n, sizeof(Point), cmp_xy);

    int m = 1;
    for (int i = 1; i < n; i++) {
        if (pts[i].x != pts[m - 1].x || pts[i].y != pts[m - 1].y) {
            pts[m++] = pts[i];
        }
    }
    return m;
}

int min_yx_index(const Point *pts, int n) {
    int idx = 0;
    for (int i = 1; i < n; i++) {
        if (pts[i].y < pts[idx].y ||
            (pts[i].y == pts[idx].y && pts[i].x < pts[idx].x)) {
            idx = i;
        }
    }
    return idx;
}

void rotate_to_min_yx(Point *pts, int n) {
    if (n <= 1) return;
    int k = min_yx_index(pts, n);
    if (k == 0) return;

    Point *tmp = (Point *)malloc((size_t)n * sizeof(Point));
    if (tmp == NULL) return;

    int t = 0;
    for (int i = k; i < n; i++) tmp[t++] = pts[i];
    for (int i = 0; i < k; i++) tmp[t++] = pts[i];
    for (int i = 0; i < n; i++) pts[i] = tmp[i];
    free(tmp);
}

int graham_scan(Point *pts, int n, Point *hull) {
    if (n == 0) return 0;
    if (n == 1) {
        hull[0] = pts[0];
        return 1;
    }

    int pivot_idx = min_yx_index(pts, n);
    Point tmp = pts[0];
    pts[0] = pts[pivot_idx];
    pts[pivot_idx] = tmp;
    g_pivot = pts[0];

    if (n > 1) {
        qsort(pts + 1, (size_t)(n - 1), sizeof(Point), cmp_polar);
    }

    hull[0] = pts[0];
    hull[1] = pts[1];
    int top = 1;

    for (int i = 2; i < n; i++) {
        while (top >= 1 && cross(hull[top - 1], hull[top], pts[i]) <= 0) {
            top--;
        }
        hull[++top] = pts[i];
    }

    int m = top + 1;
    rotate_to_min_yx(hull, m);
    return m;
}

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
