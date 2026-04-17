#include "hull.h"

#include <stddef.h>
#include <stdlib.h>

static Point g_pivot; // head of sorted points (also leftmost point)

static int cmp_xy(const void *a, const void *b) {
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

static int cmp_polar(const void *a, const void *b) {
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
    // NOTE: this should be replaced by a proved version
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

int build_hull_from_sorted_tail(Point pivot, const Point *sorted_tail, int tail_n, Point *hull) {
    if (tail_n < 0) return 0;

    hull[0] = pivot;
    int top = 0;

    /*
     * Rocq-side iterator consumes `rev l`, so we scan tail from end to start.
     * The pop condition mirrors `cross(...) <= 0`.
     */
    for (int i = tail_n - 1; i >= 0; i--) {
        while (top >= 1 && cross(hull[top - 1], hull[top], sorted_tail[i]) <= 0) {
            top--;
        }
        hull[++top] = sorted_tail[i];
    }

    int m = top + 1;
    rotate_to_min_yx(hull, m);
    return m;
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

    qsort(pts + 1, (size_t)(n - 1), sizeof(Point), cmp_polar);

    /*
     * Adapter layer:
     * - UVA preprocessing here gives a forward polar order.
     * - Rocq refinement function consumes points as `rev l`.
     * Reverse once here so `build_hull_from_sorted_tail` sees the intended order.
     */
    int tail_n = n - 1;
    Point *rocq_tail = (Point *)malloc((size_t)tail_n * sizeof(Point));
    if (rocq_tail == NULL) return 0;

    for (int i = 0; i < tail_n; i++) {
        rocq_tail[i] = pts[n - 1 - i];
    }

    int m = build_hull_from_sorted_tail(pts[0], rocq_tail, tail_n, hull);
    free(rocq_tail);
    return m;
}
