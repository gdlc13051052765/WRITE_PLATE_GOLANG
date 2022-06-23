package main

//ip地址信息结构体
type _IpMessage struct {
	localip     string
	mask        string
	gateway     string
	routeip     string
	port        string
	stationcode string
	maincode    string
	nonet       string
}

//设备信息结构体
type _DevMsgCon struct {
	clientID     string //客户端ID
	clientSecret string //客户端密钥
	devtype      string //设备类型
}
