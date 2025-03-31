# TODO

## Graham's Scan (扫描线)

证明目标

1. 算法得到凸多边形 x

2. 算法得到的三角形分割构成凸包 [x]

point_in_triangle 当前定义处理共线情况有误

- 修改 point_in_tri 引理
  at_mid: 

3. 算法得到的凸多边形包含所有点 [TODO]

3.1. 凸包定义等价 (triangle <-> edge)

point_in_hull  : ⋃ 起始点与各边构成的三角形内部
point_in_hull' : ⋂ 每条边左侧

point_in_hull' p p0 [p1 .. pn] := (recur) leftequal p0->pi p0->p /\ leftequal pn->p0 pn->p
