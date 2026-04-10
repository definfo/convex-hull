# C. Convex Hull Extension

| | |
|---|---|
| Time limit | 4 seconds |
| Memory limit | 1024 MB |

## Problem

Dr. Hugh Klidd is a geometry expert who has recently become preoccupied with convex hulls. Recall that for a set of points in the x-y plane, the convex hull is the smallest convex polygon containing all of those points. (A convex polygon has the property that for any two points on/in the polygon, the line segment connecting those two points lies entirely on/in the polygon.) Dr. Klidd has just computed the convex hull of a set of points, *S*, which he denotes *H(S)*, and is quite pleased with the result:

- the convex hull has *n* ≥ 3 vertices
- each vertex has integer coordinates
- no three of the convex hull vertices are collinear, i.e., lie on the same line

Dr. Klidd is ambitious, though, so he wants this convex hull to grow. Specifically, he is looking for an **extension point**, which is a point *p* = (*x*, *y*) satisfying the following conditions:

1. *x* and *y* are integers
2. if *S*′ = *S* ∪ {*p*} (*S* with *p* added), then the convex hull of *S*′, i.e., *H(S*′*)*, has *n* + 1 vertices
3. no three of these *n* + 1 vertices are collinear

In other words, an extension point increases the number of convex hull vertices by 1, while still keeping all its nice properties. For most convex hulls *H(S)*, Dr. Klidd can usually find at least one extension point, but he would like to know **how many** extension points there are to choose from. He postulates that there is an efficient way to count the number of extension points, but having never taken an algorithms course, he turns to you for help.

![Illustration of an extension point for Sample Input 1](ECNA2023C_1.png)

## Input

- The first line contains an integer **n** (3 ≤ n ≤ 50), the number of vertices of the convex hull.
- This is followed by **n** lines, each containing two space-separated integers — the *x* and *y* coordinates of one vertex (−1000 ≤ *x*, *y* ≤ 1000).
- The *n* points are distinct, no three are collinear, and they are given in **counterclockwise order**.

## Output

If the number of extension points is infinite, output `infinitely many`. Otherwise, output the number of extension points.

## Examples

### Example 1

**Input:**
```
5
0 2
-2 0
-1 -3
1 -3
2 1
```

**Output:**
```
23
```

### Example 2

**Input:**
```
4
-7 -7
7 -7
7 7
-7 7
```

**Output:**
```
infinitely many
```

**Explanation:** The convex hull is a square. Any integer point on the outward extension of an edge is an extension point — and there are infinitely many such points along the lines extending each edge outward.

## Note

Dr. Klidd has postulated exactly four things before now, so this is his fifth postulate.


### AI Explanation

Problem summary: Given a convex hull with n vertices (integer coordinates, CCW order), count the number of integer points p such that adding p to the point set produces a convex hull with exactly n + 1 vertices and no three vertices collinear. If the count is infinite, output "infinitely many".

Key observations:

1. Where can an extension point go? It must lie strictly outside the current hull but inside the "extended wedge" formed by extending two adjacent edges outward. Specifically, for each edge (vi, vi+1), an extension point that makes vi+1 no longer a hull vertex (replaced by p) must lie in the exterior region delimited by the lines through (vi−1, vi) and (vi+1, vi+2) extended outward — effectively "beveling" a vertex.

More precisely: p must lie outside the hull, on the outward side of exactly one edge, and on the inward (or on) side of all other edges. This means p must be in the region outside one specific edge but still "visible" from the hull.
2. When is the count infinite? When the outward region for some edge extends infinitely — i.e., the two adjacent edge lines are parallel (or the outward wedge is unbounded). This happens when consecutive edges have the same slope direction. Example 2 (a square): each pair of opposite edges is parallel, so extending any edge outward gives an infinite half-strip of integer points.
3. When finite, count lattice points in the bounded region outside each edge. For n ≤ 50 and coordinates ≤ 1000, each region is small enough to count directly or via Pick's theorem.
4. Algorithm sketch: For each edge, compute the outward feasible region (intersection of half-planes from other edges + the exterior of this edge). Check if it's bounded. If bounded, count integer points via enumeration or area-based methods. If unbounded for any edge, answer is "infinitely many".
