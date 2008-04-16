//------- Constants --------
float4x4 xView;
float4x4 xProjection;
float4x4 xWorld;
float4x4 xWorldViewProjection;
float3 xLightPosition;
float xLightPower;
float4 xAmbient;
bool xEnableLighting;
bool xEnabledTextures;

//------- Texture Samplers --------

Texture xWaterTexture;
sampler WaterTextureSampler = sampler_state { texture = <xWaterTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xSandTexture;
sampler SandTextureSampler = sampler_state { texture = <xSandTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xStoneTexture;
sampler StoneTextureSampler = sampler_state { texture = <xStoneTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xErrorTexture;
sampler ErrorTextureSampler = sampler_state { texture = <xErrorTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

//------- Technique: MultiTextured --------

float DotProduct(float3 LightPos, float3 Pos3D, float3 Normal)
{
    float3 LightDir = normalize(LightPos - Pos3D);
    return dot(LightDir, Normal);
}

struct MultiTexturedVertexToPixel
{
    float4 Position         : POSITION;    
    float4 TextureCoords    : TEXCOORD0;
    float4 TextureWeights   : TEXCOORD1;
    float3 Position3D       : TEXCOORD2;
    float3 Normal           : TEXCOORD3;
    float  Depth            : TEXCOORD4;
};

struct MultiTexturedPixelToFrame
{
    float4 Color : COLOR0;
};


//The vertex shader (VS). It returns the struct above.
MultiTexturedVertexToPixel MultiTexturedVS( float4 inPos : POSITION, float3 inNormal: NORMAL, float4 inTexCoords: TEXCOORD0, float4 inTexWeights: TEXCOORD1)
{
    MultiTexturedVertexToPixel Output = (MultiTexturedVertexToPixel)0;
    
    Output.Position       = mul(inPos, xWorldViewProjection);
    Output.TextureCoords  = inTexCoords;
    Output.TextureWeights = inTexWeights;
    Output.Position3D     = mul(inPos, xWorld);
    Output.Normal         = mul(normalize(inNormal), xWorld);
	Output.Depth          = Output.Position.z;
	 
    return Output;    
}

//The actual pixel shader. The output colour of each pixel is the sum of the colours*weights for each texture.
MultiTexturedPixelToFrame MultiTexturedPS(MultiTexturedVertexToPixel PSIn)
{
    MultiTexturedPixelToFrame Output = (MultiTexturedPixelToFrame)0;

	float textureDetailBlendThreshold   = 60;
	float textureDetailBlendDistance       = 60;
	float textureDetailBlendFactor = clamp((PSIn.Depth - textureDetailBlendThreshold) / textureDetailBlendDistance, 0, 1);

	float4 lessDetailedColor;
	float4 moreDetailedColor;
	
	lessDetailedColor  = tex2D(WaterTextureSampler, PSIn.TextureCoords) * PSIn.TextureWeights.x;
	lessDetailedColor += tex2D( SandTextureSampler, PSIn.TextureCoords) * PSIn.TextureWeights.y;
	lessDetailedColor += tex2D(StoneTextureSampler, PSIn.TextureCoords) * PSIn.TextureWeights.z;
	lessDetailedColor += tex2D(ErrorTextureSampler, PSIn.TextureCoords) * PSIn.TextureWeights.w;

	float4 foo = PSIn.TextureCoords*5;
	moreDetailedColor  = tex2D(WaterTextureSampler, foo) * PSIn.TextureWeights.x;
	moreDetailedColor += tex2D( SandTextureSampler, foo) * PSIn.TextureWeights.y;
	moreDetailedColor += tex2D(StoneTextureSampler, foo) * PSIn.TextureWeights.z;
	moreDetailedColor += tex2D(ErrorTextureSampler, foo) * PSIn.TextureWeights.w;


	Output.Color = (lessDetailedColor * textureDetailBlendFactor) + (moreDetailedColor * (1 - textureDetailBlendFactor));

	if (xEnableLighting)
	{
		float DiffuseLightingFactor = DotProduct(xLightPosition, PSIn.Position3D, PSIn.Normal);
	    Output.Color = Output.Color * DiffuseLightingFactor * xLightPower;
	}

    return Output;
}

//The definition of the Shaders for the "MultiTextured" technique
technique MultiTextured
{
    pass Pass0
    {
        VertexShader = compile vs_1_1 MultiTexturedVS();
        PixelShader = compile ps_2_0 MultiTexturedPS();
    }
}
