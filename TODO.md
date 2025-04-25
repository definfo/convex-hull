# TODO

## Graham's Scan (扫描线)

证明目标

1. 算法得到凸多边形 (DONE)

2. 算法得到的三角形分割构成凸包 (DONE, point_in_tri TODO)

3. 算法得到的凸多边形包含所有点 (WIP)

3.1. 凸包定义等价 (triangle <-> edge)

point_in_hull  : ⋃ 起始点与各边构成的三角形内部
point_in_hull_edges : ⋂ 每条边左侧
